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

    method SetEncryptionContext(encryptionContext: EncryptionContext.Map)
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

  predicate ValidHeaderBodyInRequest(headerBody: Msg.HeaderBody, request: EncryptRequest)
    reads request
  {
    headerBody.Valid()
    && headerBody.version == Msg.VERSION_1
    && headerBody.typ == Msg.TYPE_CUSTOMER_AED
    // TODO add constraint: Algorithm Suite ID: MUST be the algorithm suite used in this behavior (Note AlgID does not have to be the same as the Alg id from the request)
    // TODO add constraint: AAD: MUST be the serialization of the encryption context in the encryption materials
    // TODO add constraint: Encrypted Data Keys: MUST be the serialization of the encrypted data keys in the encryption materials
    && headerBody.contentType == Msg.ContentType.Framed
    && headerBody.frameLength == if request.frameLength.Some? then request.frameLength.get else DEFAULT_FRAME_LENGTH
  }

  predicate ValidHeaderAuthenticationInRequest(headerAuthentication: Msg.HeaderAuthentication, headerBody: Msg.HeaderBody)
    requires headerBody.Valid()
  {
    var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), _ => 0)
    && Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody)
    && exists encryptionOutput: AESEncryption.EncryptionOutput, cipherkey: seq<uint8> | 
      IsDerivedKey(cipherkey) :: AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, cipherkey)
  }

  predicate ValidFramesInRequest(frames: seq<MessageBody.Frame>, request: EncryptRequest, headerBody: Msg.HeaderBody)
    reads request
  {
    MessageBody.ValidFrames(frames)
    && |frames| < UINT32_LIMIT
    && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid())
    && MessageBody.FramesEncryptPlaintext(frames, request.plaintext) // This requirement is missing in spec but needed
    && (forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == headerBody.algorithmSuiteID.IVLength())
    && (exists cipherkey | IsDerivedKey(cipherkey) :: 
       (forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, cipherkey)))
    /**
    TODO: Add the following postconditions to MessageBody 
    IV: MUST be the sequence number used in the message body AAD for this frame.
    Encrypted Content: MUST be the output of the authenticated encryption algorithm specified by the algorithm suite, with the following inputs:
      The AAD is the serialized message body AAD
      The cipherkey is the derived data key
      Authentication Tag: MUST be the authentication tag outputted by the above encryption.
                  */
  }

  predicate ValidSignature(signature: seq<uint8>, serializedMessage: seq<uint8>)
  {
    |signature| < UINT16_LIMIT
    // TODO: the signature key is the signing key in the encryption materials
    && (exists cipherkey :: Signature.IsSigned(cipherkey, serializedMessage, signature))
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
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.algorithmSuiteID.Some? && request.algorithmSuiteID.get !in AlgorithmSuite.VALID_IDS ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.get == 0 ==> res.Failure?
    ensures match res 
      case Failure(e) => true
      case Success(encryptedSequence) =>
        // Result contains a valid serialized headerBody
        exists headerBody: Msg.HeaderBody  | ValidHeaderBodyInRequest(headerBody, request) ::
          var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
          // Result contains of a valid serialized headerAuthentication
          exists headerAuthentication | ValidHeaderAuthenticationInRequest(headerAuthentication, headerBody) ::
            var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag;
            // Result contains of a valid sequence of frames
            exists frames | ValidFramesInRequest(frames, request, headerBody) ::
              var serializedFrames := MessageBody.FramesToSequence(frames);

              // If result needs to be signed then the result contains a signature:  
              (headerBody.algorithmSuiteID.SignatureType().Some? ==> 
                exists signature | ValidSignature(signature, serializedHeaderBody + serializedHeaderAuthentication + serializedFrames) ::
                  var serializedSignature := UInt16ToSeq(|signature| as uint16) + signature;
                          encryptedSequence == serializedHeaderBody + serializedHeaderAuthentication + serializedFrames + serializedSignature)

              // If result does not need to be signed then the result is:  
              && headerBody.algorithmSuiteID.SignatureType().None? ==>
                    encryptedSequence == serializedHeaderBody + serializedHeaderAuthentication + serializedFrames
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
    assert ValidHeaderBodyInRequest (headerBody, request);
    ghost var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    
    var wr := new Streams.ByteWriter();
    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();
    assert unauthenticatedHeader == serializedHeaderBody;
    
    var iv: seq<uint8> := seq(encMat.algorithmSuiteID.IVLength(), _ => 0);
    var encryptionOutput :- AESEncryption.AESEncryptExtern(encMat.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    
    assert ValidHeaderAuthenticationInRequest(headerAuthentication, headerBody) by{
      assert headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), _ => 0);
      assert Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody);
      assert IsDerivedKey(derivedDataKey) && AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, derivedDataKey);
    }
    ghost var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag; 
    
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, encMat.algorithmSuiteID);
    assert wr.GetDataWritten() == serializedHeaderBody + serializedHeaderAuthentication;
    
    // Encrypt the given plaintext into the message body and add a footer with a signature, if required
    var seqWithGhostFrames :- MessageBody.EncryptMessageBody(request.plaintext, frameLength as int, messageID, derivedDataKey, encMat.algorithmSuiteID);
    var body := seqWithGhostFrames.sequence;
    ghost var frames := seqWithGhostFrames.frames;
    
    assert ValidFramesInRequest(frames, request, headerBody) && body == MessageBody.FramesToSequence(frames) by {
      assert MessageBody.ValidFrames(frames);
      assert |frames| < UINT32_LIMIT;
      assert forall frame: MessageBody.Frame | frame in frames :: frame.Valid();
      assert MessageBody.FramesEncryptPlaintext(frames, request.plaintext); // This requirement is missing in spec but needed
      assert forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == headerBody.algorithmSuiteID.IVLength();
      assert IsDerivedKey(derivedDataKey); 
      assert forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, derivedDataKey);
    }

    var msg := wr.GetDataWritten() + body;
    if encMat.algorithmSuiteID.SignatureType().Some? {
      var ecdsaParams := encMat.algorithmSuiteID.SignatureType().get;
      var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.get, msg);
      if |bytes| != ecdsaParams.SignatureLength() as int {
        return Failure("Malformed response from Sign().");
      }
      var signature := UInt16ToSeq(|bytes| as uint16) + bytes; 
      assert ValidSignature(bytes, msg) by{
        assert |signature| < UINT16_LIMIT;
        assert Signature.IsSigned(encMat.signingKey.get, msg, bytes)  ;
      }
      msg := msg + signature; 
      assert headerBody.algorithmSuiteID.SignatureType().Some?;
      return Success(msg);
    } else {
      // don't use a footer
      return Success(msg);
    }
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID) returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
    ensures IsDerivedKey(derivedDataKey)
  {
    var algorithm := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if algorithm == KeyDerivationAlgorithms.IDENTITY {
      assert IsDerivedKey(plaintextDataKey) by {
        reveal IsDerivedKey();
      }
      return plaintextDataKey;
    }

    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.Hkdf(algorithm, None, plaintextDataKey, infoSeq, len);
    assert IsDerivedKey(derivedKey) by {
      reveal IsDerivedKey();
    }
    return derivedKey;
  }

  predicate {:opaque} IsDerivedKey(derivedDataKey: seq<uint8>)
  {
    true
  }

 /*
  * Deserialize a message and decrypt into a plaintext.
  */
  method Decrypt(request: DecryptRequest) returns (res: Result<seq<uint8>>)
    requires request.cmm != null ==> request.cmm.Valid()
    requires request.keyring != null ==> request.keyring.Valid()
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
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
        var signatureVerified :- Signature.Verify(ecdsaParams, decMat.verificationKey.get, msg, sig);
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
