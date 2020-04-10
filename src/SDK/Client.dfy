include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "EncryptionContext.dfy"
include "CMM/Defs.dfy"
include "CMM/DefaultCMM.dfy"
include "MessageHeader.dfy"
include "MessageBody.dfy"
include "Serialize.dfy"
include "Deserialize.dfy"
include "Keyring/Defs.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/KeyDerivationAlgorithms.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"

module {:extern "ESDKClient"} ESDKClient {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionContext
  import AlgorithmSuite
  import AESEncryption
  import CMMDefs
  import DefaultCMMDef
  import Deserialize
  import HKDF
  import KeyringDefs
  import KeyDerivationAlgorithms
  import Materials
  import Msg = MessageHeader
  import MessageBody
  import Random
  import Serialize
  import Signature
  import Streams

  const DEFAULT_FRAME_LENGTH: uint32 := 4096

  class EncryptRequest {
    var plaintext: seq<uint8>
    var cmm: CMMDefs.CMM?
    var keyring: KeyringDefs.Keyring?
    var plaintextLength: nat
    var encryptionContext: EncryptionContext.Map
    var algorithmSuiteID: Option<uint16>
    var frameLength: Option<uint32>

    constructor WithKeyring(plaintext: seq<uint8>, keyring: KeyringDefs.Keyring)
      requires keyring.Valid()
      ensures |this.plaintext| == this.plaintextLength
      ensures this.keyring == keyring
      ensures this.encryptionContext == map[]
      ensures this.cmm == null
      ensures this.algorithmSuiteID.None?
      ensures this.frameLength.None?
    {
      this.plaintext := plaintext;
      this.cmm := null;
      this.keyring := keyring;
      this.plaintextLength := |plaintext|;
      this.encryptionContext := map[];
      this.algorithmSuiteID := None;
      this.frameLength := None;
    }

    constructor WithCMM(plaintext: seq<uint8>, cmm: CMMDefs.CMM)
      requires cmm.Valid()
      ensures |this.plaintext| == this.plaintextLength
      ensures this.cmm == cmm
      ensures this.encryptionContext == map[]
      ensures this.keyring == null
      ensures this.algorithmSuiteID.None?
      ensures this.frameLength.None?
    {
      this.plaintext := plaintext;
      this.cmm := cmm;
      this.keyring := null;
      this.plaintextLength := |plaintext|;
      this.encryptionContext := map[];
      this.algorithmSuiteID := None;
      this.frameLength := None;
    }

    method SetEncryptionContext(encryptionContext: EncryptionContext.Map
      modifies `encryptionContext
      ensures this.encryptionContext == encryptionContext
    {
      this.encryptionContext := encryptionContext;
    }

    method SetAlgorithmSuiteID(algorithmSuiteID: uint16)
      modifies `algorithmSuiteID
      ensures this.algorithmSuiteID == Some(algorithmSuiteID)
    {
      this.algorithmSuiteID := Some(algorithmSuiteID);
    }

    method SetFrameLength(frameLength: uint32)
      modifies `frameLength
      ensures this.frameLength == Some(frameLength)
    {
      this.frameLength := Some(frameLength);
    }
  }

  class DecryptRequest {
    var message: seq<uint8>
    var cmm: CMMDefs.CMM?
    var keyring: KeyringDefs.Keyring?

    constructor WithCMM(message: seq<uint8>, cmm: CMMDefs.CMM)
      requires cmm.Valid()
      ensures this.message== message
      ensures this.cmm == cmm
      ensures this.keyring == null
    {
      this.message := message;
      this.cmm := cmm;
      this.keyring := null;
    }

    constructor WithKeyring(message: seq<uint8>, keyring: KeyringDefs.Keyring)
      requires keyring.Valid()
      ensures this.message == message
      ensures this.keyring == keyring
      ensures this.cmm == null
    {
      this.message := message;
      this.cmm := null;
      this.keyring := keyring;
    }
  }

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(request: EncryptRequest) returns (res: Result<seq<uint8>>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
    modifies if request.cmm == null then {} else request.cmm.Repr
    ensures request.cmm != null ==> request.cmm.Valid()
    ensures request.cmm != null ==> fresh(request.cmm.Repr - old(request.cmm.Repr))
    ensures request.frameLength.Some? && request.frameLength.get == 0 ==> res.Failure?
  {
    if request.cmm != null && request.keyring != null {
      return Failure("EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both).");
    } else if request.cmm == null && request.keyring == null {
      return Failure("EncryptRequest.cmm and EncryptRequest.keyring cannot both be null.");
    } else if request.algorithmSuiteID.Some? && request.algorithmSuiteID.get !in AlgorithmSuite.VALID_IDS {
      return Failure("Invalid algorithmSuiteID.");
    } else if request.frameLength.Some? && request.frameLength.get == 0 {
      return Failure("Request frameLength must be > 0");
    }

    var cmm: CMMDefs.CMM;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }

    var frameLength := if request.frameLength.Some? then request.frameLength.get else DEFAULT_FRAME_LENGTH;

    var algorithmSuiteID := if request.algorithmSuiteID.Some? then Some(request.algorithmSuiteID.get as AlgorithmSuite.ID) else None;

    var encMatRequest := Materials.EncryptionMaterialsRequest(request.encryptionContext, algorithmSuiteID, Some(request.plaintextLength as nat));
    var encMat :- cmm.GetEncryptionMaterials(encMatRequest);
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure("Number of EDKs exceeds the allowed maximum.");
    }

    var messageID: Msg.MessageID :- Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.get, encMat.algorithmSuiteID, messageID);

    // Assemble and serialize the header and its authentication tag
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
    var body :- MessageBody.EncryptMessageBody(request.plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);
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
  method Decrypt(request: DecryptRequest) returns (res: Result<seq<uint8>>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
  {
    if request.cmm != null && request.keyring != null {
      return Failure("DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
    } else if request.cmm == null && request.keyring == null {
      return Failure("DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");
    }

    var cmm: CMMDefs.CMM;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }

    var rd := new Streams.ByteReader(request.message);
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
        assert usedCapacity <= |request.message|;
        var msg := request.message[..usedCapacity];  // unauthenticatedHeader + authTag + body  // TODO: there should be a better way to get this
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
