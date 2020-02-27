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
include "../Crypto/KeyDerivationAlgorithms.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"

module {:extern "ESDKClient"} ESDKClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite
  import CMMDefs
  import Msg = MessageHeader
  import MessageBody
  import Serialize
  import Random
  import KeyDerivationAlgorithms
  import Streams
  import HKDF
  import AESEncryption
  import Signature
  import Deserialize

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(plaintext: seq<uint8>, cmm: CMMDefs.CMM, encryptionContext: Materials.EncryptionContext) returns (res: Result<seq<uint8>>)
    requires encryptionContext.Keys !! Materials.ReservedKeyValues
    requires cmm.Valid() && Msg.ValidAAD(encryptionContext)
  {
    var encMatRequest := Materials.EncryptionMaterialsRequest(encryptionContext, None, Some(|plaintext|));
    var encMat :- cmm.GetEncryptionMaterials(encMatRequest);
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure("Number of EDKs exceeds the allowed maximum.");
    }

    var messageID: Msg.MessageID :- Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.get, encMat.algorithmSuiteID, messageID);

    // Assemble and serialize the header and its authentication tag
    var frameLength := 4096;
    var headerBody := Msg.HeaderBody(
      Msg.VERSION_1,
      Msg.TYPE_CUSTOMER_AED,
      encMat.algorithmSuiteID,
      messageID,
      encMat.encryptionContext,
      Msg.EncryptedDataKeys(encMat.encryptedDataKeys),
      Msg.ContentType.Framed,
      encMat.algorithmSuiteID.IVLength() as uint8,
      frameLength);
    var wr := new Streams.ByteWriter();

    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();

    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);

    // Encrypt the given plaintext into the message body and add a footer with a signature, if required
    var body :- MessageBody.EncryptMessageBody(plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);
    var msg := wr.GetDataWritten() + body;

    match encMat.algorithmSuiteID.SignatureType() {
      case None =>
        // don't use a footer
      case Some(ecdsaParams) =>
        var digest :- Signature.Digest(ecdsaParams, msg);
        var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
        if |bytes| != ecdsaParams.SignatureLength() as int {
          return Failure("Malformed response from Sign().");
        }
        msg := msg + UInt16ToSeq(|bytes| as uint16) + bytes;
    }

    return Success(msg);
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID) returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
  {
    var algorithm := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if algorithm == KeyDerivationAlgorithms.IDENTITY {
      return plaintextDataKey;
    }

    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.Hkdf(algorithm, None, plaintextDataKey, infoSeq, len);
    return derivedKey;
  }

 /*
  * Deserialize a message and decrypt into a plaintext.
  */
  method Decrypt(message: seq<uint8>, cmm: CMMDefs.CMM) returns (res: Result<seq<uint8>>)
    requires cmm.Valid()
  {
    var rd := new Streams.ByteReader(message);
    var header :- Deserialize.DeserializeHeader(rd);
    var decMatRequest := Materials.DecryptionMaterialsRequest(header.body.algorithmSuiteID, header.body.encryptedDataKeys.entries, header.body.aad);
    var decMat :- cmm.DecryptMaterials(decMatRequest);

    var decryptionKey := DeriveKey(decMat.plaintextDataKey.get, decMat.algorithmSuiteID, header.body.messageID);

    // Parse and decrypt the message body
    var plaintext;
    match header.body.contentType {
      case NonFramed =>
        plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.messageID);
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.frameLength as int, header.body.messageID);
    }

    match decMat.algorithmSuiteID.SignatureType() {
      case None =>
        // there's no footer
      case Some(ecdsaParams) =>
        var usedCapacity := rd.GetSizeRead();
        assert usedCapacity <= |message|;
        var msg := message[..usedCapacity];  // unauthenticatedHeader + authTag + body  // TODO: there should be a better way to get this
        // read signature
        var signatureLength :- rd.ReadUInt16();
        var sig :- rd.ReadBytes(signatureLength as nat);
        // verify signature
        var digest :- Signature.Digest(ecdsaParams, msg);
        var signatureVerified :- Signature.Verify(ecdsaParams, decMat.verificationKey.get, digest, sig);
        if !signatureVerified {
          return Failure("signature not verified");
        }
    }

    var isDone := rd.IsDoneReading();
    if !isDone {
      return Failure("message contains additional bytes at end");
    }

    return Success(plaintext);
  }
}
