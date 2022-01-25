// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Serialize/EncryptionContext.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../AwsCryptographicMaterialProviders/Materials.dfy"
include "MessageBody.dfy"
include "../Crypto/Random.dfy"
include "../Util/Streams.dfy"
include "../Crypto/HKDF/HKDF.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Signature.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "Serialize/SerializableTypes.dfy"

include "Serialize/Header.dfy"
include "Serialize/HeaderTypes.dfy"
include "Serialize/V1HeaderBody.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/SerializeFunctions.dfy"


module {:extern "EncryptDecrypt"} EncryptDecrypt {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Aws.Crypto
  import EncryptionContext
  import AESEncryption
  import MaterialProviders.Client
  import HKDF
  import MaterialProviders.Materials
  import MessageBody
  import Random
  import Signature
  import Streams
  import SerializableTypes
  import opened SerializeFunctions

  import Header
  import HeaderTypes
  import HeaderAuth
  import V1HeaderBody

  const DEFAULT_FRAME_LENGTH: uint32 := 4096

  datatype EncryptRequest = EncryptRequest(
    plaintext: seq<uint8>,
    cmm: Crypto.ICryptographicMaterialsManager?,
    keyring: Crypto.IKeyring?,
    plaintextLength: nat,
    encryptionContext: Crypto.EncryptionContext,
    algorithmSuiteID: Option<Crypto.AlgorithmSuiteId>,
    frameLength: Option<uint32>)
  {
    static function method WithCMM(plaintext: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager): EncryptRequest
    {
      EncryptRequest(plaintext, cmm, null, |plaintext|, map[], None, None)
    }

    static function method WithKeyring(plaintext: seq<uint8>, keyring: Crypto.IKeyring): EncryptRequest
    {
      EncryptRequest(plaintext, null, keyring, |plaintext|, map[], None, None)
    }

    function method SetEncryptionContext(encryptionContext: Crypto.EncryptionContext): EncryptRequest {
      this.(encryptionContext := encryptionContext)
    }

    function method SetAlgorithmSuiteID(algorithmSuiteID: Crypto.AlgorithmSuiteId): EncryptRequest {
      this.(algorithmSuiteID := Some(algorithmSuiteID))
    }

    function method SetFrameLength(frameLength: uint32): EncryptRequest {
      this.(frameLength := Some(frameLength))
    }
  }

  datatype DecryptRequest = DecryptRequest(message: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager?, keyring: Crypto.IKeyring?)
  {
    static function method WithCMM(message: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager): DecryptRequest
    {
      DecryptRequest(message, cmm, null)
    }

    static function method WithKeyring(message: seq<uint8>, keyring: Crypto.IKeyring): DecryptRequest
    {
      DecryptRequest(message, null, keyring)
    }
  }

  // // Specification of Encrypt with signature
  function method SerializeMessageWithSignature(
    framedMessage: MessageBody.FramedMessage,
    signature: seq<uint8>
  )
    :(message: seq<uint8>)
    requires |signature| < UINT16_LIMIT
    ensures message
    == SerializeMessageWithoutSignature(framedMessage) + WriteShortLengthSeq(signature)
  {
    SerializeMessageWithoutSignature(framedMessage) + WriteShortLengthSeq(signature)
  }

  // // Specification of Encrypt without signature
  function method SerializeMessageWithoutSignature(
    framedMessage: MessageBody.FramedMessage
  )
    :(message: seq<uint8>)
  {
    // The header
    framedMessage.finalFrame.header.rawHeader
    // The header authentication
    + HeaderAuth.WriteAESMac(framedMessage.finalFrame.header.headerAuth)
    // The message body i.e. "all the frames"
    + MessageBody.WriteFramedMessageBody(framedMessage)
  }

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(request: EncryptRequest)
      returns (res: Result<seq<uint8>, string>)
              //  ,ghost successSupportingInfo: Option<(Msg.HeaderBody, Msg.HeaderAuthentication, seq<MessageBody.Frame>, seq<uint8>)>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.value == 0 ==> res.Failure?
    // TODO: Need to add back proof
    // ensures match res
    //   case Failure(e) => true
    //   case Success(encryptedSequence) =>
    //     && successSupportingInfo.Some?
    //     && var Some((headerBody, headerAuthentication, frames, signature)) := successSupportingInfo;
    //     // The result is a serialization of 3 items with a potential fourth item.
    //     // Every item has to meet some specification which is specified in its respective section
    //     && ValidHeaderBodyForRequest(headerBody, request) // Which meet their respective specifications
    //     && ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody)
    //     && ValidFramesForRequest(frames, request, headerBody)
    //     && match Client.SpecificationClient().GetSuite(SerializableTypes.GetAlgorithmSuiteId(headerBody.algorithmSuiteID)).signature {
    //         case ECDSA(_) => // If the result needs to be signed then there exists a fourth item
    //           && ValidSignatureForRequest(signature, headerBody, headerAuthentication, frames) // which meets its specification
    //           && encryptedSequence == SerializeMessageWithSignature(headerBody, headerAuthentication, frames, signature) // These items can be serialized to the output
    //         case None => // if the result does not need to be signed
    //           encryptedSequence == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames) // Then these items can be serialized to the output
    //       }
  {
    // successSupportingInfo := None; // KRML: why is the type of "successSupportingInfo" subject to definite-assignment rules?
    // Validate encrypt request
    :- Need(request.cmm != null || request.keyring != null, "EncryptRequest.cmm OR EncryptRequest.keyring must be set.");
    :- Need(!(request.cmm != null && request.keyring != null), "EncryptRequest.keyring AND EncryptRequest.cmm must not both be set.");
    :- Need(request.frameLength.None? || request.frameLength.value > 0, "Requested frame length must be > 0");
    :- Need(request.plaintextLength < INT64_MAX_LIMIT, "Input plaintext size too large.");

    var cmm: Crypto.ICryptographicMaterialsManager;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      var client := new Client.AwsCryptographicMaterialProvidersClient();
      cmm := client
        .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
        keyring := request.keyring
      ));
    }

    var frameLength := if request.frameLength.Some? then request.frameLength.value else DEFAULT_FRAME_LENGTH;

    var algorithmSuiteID := request.algorithmSuiteID;

    var encMatRequest := Crypto.GetEncryptionMaterialsInput(
      encryptionContext:=request.encryptionContext,
      algorithmSuiteId:=algorithmSuiteID,
      maxPlaintextLength:=Option.Some(request.plaintextLength as int64)
    );

    var output :- cmm.GetEncryptionMaterials(encMatRequest);

    var encMat := output.encryptionMaterials;

    :- Need(Client.Materials.EncryptionMaterialsWithPlaintextDataKey(encMat), "CMM returned invalid EncryptionMaterials");

    // Validate encryption materials
    :- Need(SerializableTypes.IsESDKEncryptionContext(encMat.encryptionContext), "CMM failed to return serializable encryption materials.");
    :- Need(HasUint16Len(encMat.encryptedDataKeys), "CMM returned EDKs that exceed the allowed maximum.");
    :- Need(forall edk
      | edk in encMat.encryptedDataKeys
      :: SerializableTypes.IsESDKEncryptedDataKey(edk), "CMM returned non-serializable encrypted data key.");

    var encryptedDataKeys: SerializableTypes.ESDKEncryptedDataKeys := encMat.encryptedDataKeys;

    var esdkId := SerializableTypes.GetESDKAlgorithmSuiteId(encMat.algorithmSuiteId);
    var suite := Client.SpecificationClient().GetSuite(encMat.algorithmSuiteId);
    var messageID: HeaderTypes.MessageID :- Random.GenerateBytes(HeaderTypes.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.value, suite, messageID);

    var canonicalEncryptionContext := EncryptionContext.GetCanonicalEncryptionContext(encMat.encryptionContext);

    // Until the commitment policy has been plumbed through
    // we can not assert assert Header.HeaderVersionSupportsCommitment?(suite, body);
    // without the following:
    :- Need(!suite.commitment.HKDF?, "Commitment not yet supported");

    var body := HeaderTypes.HeaderBody.V1HeaderBody(
      messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
      esdkSuiteId := esdkId,
      messageId := messageID,
      encryptionContext := canonicalEncryptionContext,
      encryptedDataKeys := encryptedDataKeys,
      contentType := HeaderTypes.ContentType.Framed,
      headerIvLength := suite.encrypt.ivLength as nat,
      frameLength := frameLength
    );

    var rawHeader := Header.WriteHeaderBody(body);

    var iv: seq<uint8> := seq(suite.encrypt.ivLength as int, _ => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(suite.encrypt, iv, derivedDataKey, [], rawHeader);
    var headerAuth := HeaderTypes.HeaderAuth.AESMac(
      headerIv := iv,
      headerAuthTag := encryptionOutput.authTag
    );

    var header := Header.HeaderInfo(
      body := body,
      rawHeader := rawHeader,
      encryptionContext := encMat.encryptionContext,
      suite := suite,
      headerAuth := headerAuth
    );

    // Add headerAuth requirements to Header type
    assert Header.CorrectlyReadHeaderBody(
      ReadableBuffer(rawHeader, 0),
      Success(SuccessfulRead(body, ReadableBuffer(rawHeader, |rawHeader|))));
    assert Header.HeaderAuth?(suite, headerAuth);
    assert Header.IsHeader(header);

    // Encrypt the given plaintext into the framed message
    var framedMessage :- MessageBody.EncryptMessageBody(
      request.plaintext,
      header,
      derivedDataKey
    );

    if framedMessage.finalFrame.header.suite.signature.ECDSA? {
      var msg := SerializeMessageWithoutSignature(framedMessage);
      var ecdsaParams := framedMessage.finalFrame.header.suite.signature.curve;
      // TODO: This should just work, but Proof is difficult
      :- Need(encMat.signingKey.Some?, "Missing signing key.");

      var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.value, msg);
      :- Need(|bytes| == ecdsaParams.SignatureLength() as int, "Malformed response from Sign().");

      var signature := UInt16ToSeq(|bytes| as uint16) + bytes;
      msg := msg + signature;
      // TODO: Come back and prove this
      // assert msg == SerializeMessageWithSignature(framedMessage, signature); // Header, frames and signature can be serialized into the stream
      return Success(msg);
    } else {
      var msg := SerializeMessageWithoutSignature(framedMessage);
      return Success(msg);
    }
  }

  // This should take materials and the headerBody...
  // It should return these types together with the derived key.
  method DeriveKey(
    plaintextDataKey: seq<uint8>,
    suite: Client.AlgorithmSuites.AlgorithmSuite,
    messageID: HeaderTypes.MessageID
  ) 
    returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == suite.encrypt.keyLength as int
    ensures |derivedDataKey| == suite.encrypt.keyLength as int
    ensures IsDerivedKey(derivedDataKey)
  {
    if suite.kdf.IDENTITY? {
      assert IsDerivedKey(plaintextDataKey) by {
        reveal IsDerivedKey();
      }
      return plaintextDataKey;
    }

    var algorithmSuiteID := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var len := suite.kdf.inputKeyLength as int;
    var derivedKey := HKDF.Hkdf(suite.kdf.hmac, None, plaintextDataKey, infoSeq, len);
    assert IsDerivedKey(derivedKey) by {
      reveal IsDerivedKey();
    }
    return derivedKey;
  }

  predicate {:opaque} IsDerivedKey(derivedDataKey: seq<uint8>)
  {
    true
  }

  method Decrypt(request: DecryptRequest) returns (res: Result<seq<uint8>, string>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
  {
    var plaintext :- DecryptWithVerificationInfo(request);
    return Success(plaintext);
  }

  datatype DecryptResultWithVerificationInfo = DecryptResultWithVerificationInfo(
          plaintext: seq<uint8>,
    ghost header: Header.Header,
    ghost hbSeq: seq<uint8>,
    ghost frames: seq<MessageBody.Frame>,
    ghost signature: Option<seq<uint8>>)


  // Verification of this method requires verification of the CMM to some extent, The verification of the Decrypt method should be extended after CMM is verified
  method DecryptWithVerificationInfo(request: DecryptRequest)
    returns (res: Result<seq<uint8>, string>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    // TODO: Need to add back proof
    // ensures match res // Verify that if no error occurs the correct objects are deserialized from the stream
    //   case Failure(e) => true
    //   case Success(d) => // Unfold return value into seperate variables
    //     && d.header.body.Valid()
    //     && Msg.IsSerializationOfHeaderBody(d.hbSeq, d.header.body)
    //     && (d.header.body.contentType.Framed? ==> // We only verify framed content for now
    //       && (forall frame: MessageBody.Frame | frame in d.frames :: frame.Valid())
    //       && MessageBody.FramesEncryptPlaintext(d.frames, d.plaintext)
    //       && match d.signature {
    //            case Some(_) =>
    //              && |d.signature.value| < UINT16_LIMIT
    //              && request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag // These items can be serialized to the output
    //                + MessageBody.FramesToSequence(d.frames) + UInt16ToSeq(|d.signature.value| as uint16) + d.signature.value
    //            case None => // if the result does not need to be signed
    //              request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag + MessageBody.FramesToSequence(d.frames)
    //          })
  {
    // Validate decrypt request
    :- Need(request.cmm == null || request.keyring == null, "DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
    :- Need(request.cmm != null || request.keyring != null, "DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");

    var cmm: Crypto.ICryptographicMaterialsManager;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      var client := new Client.AwsCryptographicMaterialProvidersClient();
      cmm := client
        .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
        keyring := request.keyring
      ));
    }

    var buffer := SerializeFunctions.ReadableBuffer(request.message, 0);
    var headerBody :- Header
      .ReadHeaderBody(buffer)
      .MapFailure(MapSerializeFailure(": ReadHeaderBody"));

    var rawHeader := headerBody.tail.bytes[buffer.start..headerBody.tail.start];

    var esdkEncryptionContext := EncryptionContext.GetEncryptionContext(headerBody.data.encryptionContext);

    var decMatRequest := Crypto.DecryptMaterialsInput(
      algorithmSuiteId:=SerializableTypes.GetAlgorithmSuiteId(headerBody.data.esdkSuiteId),
      encryptedDataKeys:=headerBody.data.encryptedDataKeys,
      encryptionContext:=esdkEncryptionContext);
    var output :- cmm.DecryptMaterials(decMatRequest);
    var decMat := output.decryptionMaterials;

    // Validate decryption materials
    :- Need(Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat), "CMM returned invalid DecryptMaterials");

    var suite := Client
      .SpecificationClient()
      .GetSuite(decMat.algorithmSuiteId);

    var headerAuth :- HeaderAuth
      .ReadAESMac(headerBody.tail, suite)
      .MapFailure(MapSerializeFailure(": ReadAESMac"));

    var decryptionKey := DeriveKey(decMat.plaintextDataKey.value, suite, headerBody.data.messageId);

    // There is nothing to compare since there was nothing to decrypt.
    // Success means that the tag is correct.
    var _ :- AESEncryption.AESDecrypt(
      suite.encrypt,
      decryptionKey,
      [], // The header auth is for integrity, not confidentiality
      headerAuth.data.headerAuthTag,
      headerAuth.data.headerIv,
      rawHeader
    );

    // Need to add a message with 
    :- Need(headerBody.data.contentType.Framed?, "Fix me");


    assert {:split_here} true;
    // Currently the Encryption Context in the header MUST be the same
    // as the canonical encryption context in the header body.
    // Ideally, only the canonical encryption context needs to be serializable.
    :- Need(SerializableTypes.IsESDKEncryptionContext(decMat.encryptionContext), "CMM failed to return serializable encryption materials.");
    // The V2 message format not only supports commitment, it requires it.
    // Therefore the message format is bound to properties of the algorithm suite.
    :- Need(Header.HeaderVersionSupportsCommitment?(suite, headerBody.data), "Algorithm suite does not match message format.");

    var header := Header.HeaderInfo(
      body := headerBody.data,
      rawHeader := rawHeader,
      encryptionContext := decMat.encryptionContext,
      suite := suite,
      headerAuth := headerAuth.data
    );

    assert {:split_here} true;
    assert Header.CorrectlyReadHeaderBody(
      ReadableBuffer(rawHeader, 0),
      Success(SuccessfulRead(headerBody.data, ReadableBuffer(rawHeader, |rawHeader|))));
    assert Header.HeaderAuth?(suite, headerAuth.data);
    assert Header.IsHeader(header);

    var messageBody :- MessageBody.ReadFramedMessageBody(
      headerAuth.tail,
      header,
      [],
      headerAuth.tail
    ).MapFailure(MapSerializeFailure(": ReadFramedMessageBody"));

    assert {:split_here} true;
    assert suite == messageBody.data.finalFrame.header.suite;
    assert |decryptionKey| == messageBody.data.finalFrame.header.suite.encrypt.keyLength as int;

    // ghost var endHeaderPos := rd.reader.pos;
    // Parse the message body
    var plaintext;
    match header.body.contentType {
      case NonFramed => return Failure("not at this time");
      //   plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, suite, decryptionKey, header.body.messageID);
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(messageBody.data, decryptionKey);
    }

    var signature :- VerifySignature(
      messageBody.tail,
      messageBody.tail.bytes[buffer.start..messageBody.tail.start],
      decMat
    );

    :- Need(signature.start == |signature.bytes|, "Data after message footer.");

    return Success(plaintext);
  }

  method VerifySignature(
    buffer: SerializeFunctions.ReadableBuffer,
    msg: seq<uint8>,
    decMat: Crypto.DecryptionMaterials
  )
    returns (res: Result<SerializeFunctions.ReadableBuffer, string>)
    requires Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat)
    // TODO: Add Proof
    // ensures match res
    //   case Failure(_) => true
    //   case Success(_) =>
    //     && 2 <= old(rd.reader.pos) + 2 <= rd.reader.pos
    //     && SignatureBySequence(signature, rd.reader.data[old(rd.reader.pos)..rd.reader.pos])
  {

    // DecryptionMaterialsWithPlaintextDataKey ensures that the materials and the suite match.
    // If there is no verification key, that lets us conclude that the suite does not have a signature.
    if decMat.verificationKey.None? {
      return Success(buffer);
    }

    var signature :- SerializeFunctions
      .ReadShortLengthSeq(buffer)
      .MapFailure(MapSerializeFailure(": ReadShortLengthSeq"));

    var ecdsaParams := Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.curve;
    // verify signature
    var signatureVerifiedResult :- Signature.Verify(ecdsaParams, decMat.verificationKey.value, msg, signature.data);

    return Success(signature.tail);
  }

  predicate {:opaque } SignatureBySequence(signature: seq<uint8>, sequence: seq<uint8>)
  {
    && |signature| < UINT16_LIMIT
    && sequence == UInt16ToSeq(|signature| as uint16) + signature
  }

  lemma UpperBoundRemv(sequence: seq<uint8>, lo: int)
    requires 0 <= lo <= |sequence|
    ensures sequence[lo..|sequence|] == sequence[lo..]
  {

  }

  lemma LemmaESDKAlgorithmSuiteIdImpliesEquality(
    esdkId: SerializableTypes.ESDKAlgorithmSuiteId,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    requires SerializableTypes.GetAlgorithmSuiteId(esdkId) == suite.id
    ensures
      && var suiteId := SerializableTypes.GetAlgorithmSuiteId(esdkId);
      && Client.SpecificationClient().GetSuite(suiteId) == suite
  {
    var suiteId := SerializableTypes.GetAlgorithmSuiteId(esdkId);
    if Client.SpecificationClient().GetSuite(suiteId) != suite {
      assert Client.SpecificationClient().GetSuite(suiteId).encrypt.keyLength == suite.encrypt.keyLength;
    }
  }

  function method MapSerializeFailure(s: string): SerializeFunctions.ReadProblems -> string {
    (e: SerializeFunctions.ReadProblems) =>
    match e
      case Error(e) => e
      case MoreNeeded(_) => "Incomplete message" + s
  }

}
