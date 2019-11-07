include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "CMM/Defs.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "Deserialize.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/Digests.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"

module ESDKClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import CMMDefs
  import Msg = MessageHeader
  import MessageBody
  import Serialize
  import Random
  import Digests
  import Streams
  import HKDF
  import AESEncryption
  import Signature
  import Deserialize

  /*
   * Encrypt a plaintext and serialize it into a message.
   * Following https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/client-apis/encrypt.md, 2019-09-24.
   */
  method Encrypt(plaintext: seq<uint8>, cmm: CMMDefs.CMM, encryptionContext: Materials.EncryptionContext) returns (res: Result<seq<uint8>>)
    requires Materials.GetKeysFromEncryptionContext(encryptionContext) !! Materials.ReservedKeyValues
    requires cmm.Valid() && Msg.ValidAAD(encryptionContext)
  {
    /*
     * What's needed for the encryption: encryption materials, message ID, and derived data key.
     */

    var encMat :- cmm.GetEncryptionMaterials(encryptionContext, None, Some(|plaintext|));
    Msg.AssumeValidAAD(encMat.encryptionContext);
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure("Number of EDKs exceeds the allowed maximum.");
    }

    var messageID: Msg.MessageID := Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.get, encMat.algorithmSuiteID, messageID);

    /*
     * Assemble and serialize the header and its authentication tag.
     */

    var frameLength := 4096;
    var headerBody := Msg.HeaderBody(
      Msg.VERSION_1,
      Msg.TYPE_CUSTOMER_AED,
      encMat.algorithmSuiteID,
      messageID,
      encMat.encryptionContext,  // NOTE: This had been wrong (was "encryptionContext"). HeaderBody.Valid should say EC_PUBLIC_KEY_FIELD is a key of encryptionContext if algorithmSuiteID.SignatureType().Some?
      Msg.EncryptedDataKeys(encMat.encryptedDataKeys),
      Msg.ContentType.Framed,
      encMat.algorithmSuiteID.IVLength() as uint8,
      frameLength);
    var wr := new Streams.StringWriter();

    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.data;

    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);

    /*
     * Encrypt the given plaintext into the message body.
     */

    var body :- MessageBody.EncryptMessageBody(plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);

    /*
     * Add footer with signature, if required.
     */

    var msg := wr.data + body;

    match encMat.algorithmSuiteID.SignatureType() {
      case None =>
        // don't use a footer
      case Some(ecdsaParams) =>
        var digest := Signature.Digest(ecdsaParams, msg);
        var signResult := Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
        match signResult {
          case None =>
            return Failure("Message signing failed");
          case Some(bytes) =>
            msg := msg + UInt16ToSeq(|bytes| as uint16) + bytes;
        }
    }

    return Success(msg);
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID) returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
  {
    var whichSHA := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if whichSHA == Digests.HmacNOSHA {
      return plaintextDataKey;
    }

    var inputKeyMaterials := SeqToArray(plaintextDataKey);
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var info := SeqToArray(infoSeq);
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.hkdf(whichSHA, None, inputKeyMaterials, info, len);
    return derivedKey[..];
  }

  /*
   * Deserialize a message and decrypt into a plaintext.
   * Following https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/client-apis/decrypt.md, 2019-10-11.
   */
  method Decrypt(message: seq<uint8>, cmm: CMMDefs.CMM) returns (res: Result<seq<uint8>>)
    requires cmm.Valid()
  {
    /*
     * Parse the message header to obtain: algorithm suite ID, encrypted data keys, and encryption context.
     */

    var rd := new Streams.StringReader.FromSeq(message);
    var header :- Deserialize.DeserializeHeader(rd);

    /*
     * What's needed for the decryption: decryption materials, decryption key.
     */

    var decMat :- cmm.DecryptMaterials(header.body.algorithmSuiteID, header.body.encryptedDataKeys.entries, header.body.aad);

    var decryptionKey := DeriveKey(decMat.plaintextDataKey.get, decMat.algorithmSuiteID, header.body.messageID);

    /*
     * Parse and decrypt message body.
     */

    var plaintext;
    match header.body.contentType {
      case NonFramed =>
        // TODO
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.frameLength as int, header.body.messageID);
    }

    match decMat.algorithmSuiteID.SignatureType() {
      case None =>
        // there's no footer
      case Some(ecdsaParams) =>
        var msg := message[..rd.pos];  // unauthenticatedHeader + authTag + body  // TODO: there should be a better way to get this
        // read signature
        var signatureLength :- rd.ReadUInt16();
        var sig :- rd.ReadExact(signatureLength as nat);
        // verify signature
        var digest := Signature.Digest(ecdsaParams, msg);
        var signatureVerified := Signature.ECDSA.Verify(ecdsaParams, decMat.verificationKey.get, digest, sig);
        if !signatureVerified {
          return Failure("signature not verified");
        }
    }

    if rd.Available() != 0 {
      return Failure("message contains additional bytes at end");
    }

    return Success(plaintext);
  }
}
