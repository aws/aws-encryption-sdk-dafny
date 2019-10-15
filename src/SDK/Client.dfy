include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "CMM/Defs.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
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
      encryptionContext,
      Msg.EncryptedDataKeys(encMat.encryptedDataKeys),
      Msg.ContentType.Framed,
      [0, 0, 0, 0],
      encMat.algorithmSuiteID.IVLength() as uint8,
      frameLength);
    var wr := new Streams.StringWriter();
    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.data;

    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var pair :- MessageBody.Encrypt(encMat.algorithmSuiteID, iv, derivedDataKey, [], unauthenticatedHeader);
    assert |pair.0| == 0;
    var headerAuthentication := Msg.HeaderAuthentication(iv, pair.1);
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
        var signResult := Signature.Sign(ecdsaParams, encMat.signingKey.get, msg);
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
    requires |plaintextDataKey| == algorithmSuiteID.KeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
  {
    var whichSHA := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if whichSHA == Digests.HmacNOSHA {
      return plaintextDataKey;
    }

    var salt := new [0];
    var inputKeyMaterials := SeqToArray(plaintextDataKey);
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var info := SeqToArray(infoSeq);
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.hkdf(whichSHA, salt, inputKeyMaterials, info, len);
    return derivedKey[..];
  }
}
