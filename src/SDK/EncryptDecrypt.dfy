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
    == SerializeMessageWithoutSignature(framedMessage) + UInt16ToSeq(|signature| as uint16) + signature
  {
    var serializedSignature := UInt16ToSeq(|signature| as uint16) + signature;
    SerializeMessageWithoutSignature(framedMessage) + serializedSignature
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

  // // Specification of headerBody in Encrypt
  // predicate ValidHeaderBodyForRequest(headerBody: Msg.HeaderBody, request: EncryptRequest)
  // {
  //   && headerBody.Valid()
  //   && headerBody.version == Msg.VERSION_1
  //   && headerBody.typ == Msg.TYPE_CUSTOMER_AED
  //   // TODO This is currently failing. What is it proving and is it needed?
  //   // && (exists material: Crypto.EncryptionMaterials | DefaultCMMDef.EncryptionMaterialsSignature(material) ::
  //   // headerBody.algorithmSuiteID == AlgorithmSuite.PolymorphIDToInternalID(material.algorithmSuiteId)
  //   // && headerBody.aad == material.encryptionContext
  //   // && headerBody.encryptedDataKeys == Msg.EncryptedDataKeys(material.encryptedDataKeys))
  //   && headerBody.contentType == Msg.ContentType.Framed
  //   && headerBody.frameLength == if request.frameLength.Some? then request.frameLength.value else DEFAULT_FRAME_LENGTH
  // }

  // // Specification of headerAuthentication in Encrypt
  // predicate ValidHeaderAuthenticationForRequest(headerAuthentication: Msg.HeaderAuthentication, headerBody: Msg.HeaderBody)
  //   requires headerBody.Valid()
  // {
  //   var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
  //   var suite := Client.SpecificationClient().GetSuite(SerializableTypes.GetAlgorithmSuiteId(headerBody.algorithmSuiteID));
  //   && headerAuthentication.iv == seq(suite.encrypt.ivLength, _ => 0)
  //   && Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody)
  //   && exists encryptionOutput: AESEncryption.EncryptionOutput, cipherkey: seq<uint8> |
  //     IsDerivedKey(cipherkey) :: AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, cipherkey)
  // }

  // // Specification of the Frames used in Encrypt
  // predicate ValidFramesForRequest(frames: seq<MessageBody.Frame>, request: EncryptRequest, headerBody: Msg.HeaderBody)
  // {
  //   (forall frame: MessageBody.Frame | frame in frames :: frame.Valid()) //This predicates ensure that the frame can be converted to a sequence
  //   && MessageBody.FramesEncryptPlaintext(frames, request.plaintext) // This requirement is missing in spec but needed for now needs to be addapted to match streaming
  //   && var suite := Client.SpecificationClient().GetSuite(SerializableTypes.GetAlgorithmSuiteId(headerBody.algorithmSuiteID));
  //   && (forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == suite.encrypt.ivLength as int)
  //   && (exists cipherkey | IsDerivedKey(cipherkey) :: // The cipherkey used in the encryption is the derived key
  //      (forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, cipherkey)))
  // }

  // //Specification of the Signature used in Encrypt
  // predicate ValidSignatureForRequest(signature: seq<uint8>, headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication,frames: seq<MessageBody.Frame>)
  //   requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
  //   requires headerBody.Valid()
  // {
  //   var serializedMessage := SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames);
  //   |signature| < UINT16_LIMIT
  //   && (exists material: Crypto.EncryptionMaterials | material.signingKey.Some? ::
  //       Signature.IsSigned(material.signingKey.value, serializedMessage, signature))
  // }

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(request: EncryptRequest)
      returns (res: Result<seq<uint8>, string>)
              //  ,ghost successSupportingInfo: Option<(Msg.HeaderBody, Msg.HeaderAuthentication, seq<MessageBody.Frame>, seq<uint8>)>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.value == 0 ==> res.Failure?
    // Need to add back
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

    // assert ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody) by{ // Header confirms to specification
    //   assert {:focus} true;
    //   assert headerAuthentication.iv == seq(suite.encrypt.ivLength, _ => 0);
    //   assert Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody);
    //   assert IsDerivedKey(derivedDataKey) && AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, derivedDataKey);
    // }
    // ghost var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag;

    // var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication);
    // assert wr.GetDataWritten() == serializedHeaderBody + serializedHeaderAuthentication; // Read data contains complete header

    // assert {:focus} true;
    // Encrypt the given plaintext into the framed message
    var framedMessage :- MessageBody.EncryptMessageBody(
      request.plaintext,
      header,
      derivedDataKey
    );

    // var body := seqWithGhostFrames.sequence;
    // ghost var frames := seqWithGhostFrames.frames;

    // assert ValidFramesForRequest(frames, request, headerBody) && body == MessageBody.FramesToSequence(frames) by { // Frames meets specification
    //   assert {:focus} true;
    //   assert forall frame: MessageBody.Frame | frame in frames :: frame.Valid();
    //   assert MessageBody.FramesEncryptPlaintext(frames, request.plaintext); // This requirement is missing in spec but needed
    //   assert forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == suite.encrypt.ivLength as int;
    //   assert IsDerivedKey(derivedDataKey);
    //   assert forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, derivedDataKey);
    // }

    // var msg := wr.GetDataWritten() + body;
    if framedMessage.finalFrame.header.suite.signature.ECDSA? {
      var msg := SerializeMessageWithoutSignature(framedMessage);
      var ecdsaParams := framedMessage.finalFrame.header.suite.signature.curve;
      // This should just work, but Proof is difficult
      :- Need(encMat.signingKey.Some?, "Missing signing key.");

      var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.value, msg);
      :- Need(|bytes| == ecdsaParams.SignatureLength() as int, "Malformed response from Sign().");

      var signature := UInt16ToSeq(|bytes| as uint16) + bytes;
      // assert ValidSignatureForRequest(bytes, headerBody, headerAuthentication, frames) by { // Signature confirms to specification
      //   assert |signature| < UINT16_LIMIT;
      //   assert Signature.IsSigned(encMat.signingKey.value, msg, bytes);
      // }
      msg := msg + signature;
      // Come back and prove this
      // assert msg == SerializeMessageWithSignature(framedMessage, signature); // Header, frames and signature can be serialized into the stream
      return Success(msg); //, Some((headerBody, headerAuthentication, frames, bytes));
    } else {
      // assert {:focus} true;
      // don't use a footer
      // assert msg == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames); // Header and frames can be serialized into the stream
      var msg := SerializeMessageWithoutSignature(framedMessage);
      return Success(msg); //, Some((headerBody, headerAuthentication, frames, []));
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
    // Need to add back
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
      .MapFailure(MapSerializeFailure);

    var rawHeader := headerBody.tail.bytes[buffer.start..headerBody.tail.start];

    var esdkEncryptionContext := EncryptionContext.GetEncryptionContext(headerBody.data.encryptionContext);

    // var rd := new Streams.ByteReader(request.message);
    // var deserializeHeaderResult :- Deserialize.DeserializeHeader(rd);
    // var header := deserializeHeaderResult.header;
    // assert header.body.Valid();

    // if header.body.contentType.Framed? { // If the header is framed then the header is deserialized from the read sequence
    //   assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..rd.reader.pos]) by {
    //     reveal HeaderBySequence();
    //     assert header.body.contentType.Framed?;
    //     assert header.body.Valid();
    //     assert Msg.IsSerializationOfHeaderBody(deserializeHeaderResult.hbSeq, header.body);
    //     assert rd.reader.data[..rd.reader.pos] == deserializeHeaderResult.hbSeq + header.auth.iv + header.auth.authenticationTag;
    //   }
    //   assert DataIsFramed(request.message) by { // Predicate that holds in DataIsFramed this predicate is currently not used but is very usefull for future validation
    //     assert 0 <= rd.reader.pos <= |request.message|;
    //     assert rd.reader.data[..rd.reader.pos] == request.message[..rd.reader.pos];
    //     assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..rd.reader.pos]);
    //   }
    // }

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
      .MapFailure(MapSerializeFailure);

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
    ).MapFailure(MapSerializeFailure);

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

    // // Ghost variable contains frames which are deserialized from the data read after the header if the data is framed
    // assert header.body.contentType.Framed? ==>
    //   exists frames: seq<MessageBody.Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid())
    //     && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos..rd.reader.pos] ::
    //       && MessageBody.FramesEncryptPlaintext(frames, plaintext);
    // ghost var frames: seq<MessageBody.Frame> :| header.body.contentType.Framed? ==>
    //     && |frames| < UINT32_LIMIT
    //     && (forall frame | frame in frames :: frame.Valid())
    //     && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos..rd.reader.pos]
    //     && MessageBody.FramesEncryptPlaintext(frames, plaintext);

    // if header.body.contentType.Framed? {
    //   assert FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]) by {
    //     reveal FramesBySequence();
    //     assert |frames| < UINT32_LIMIT;
    //     assert forall frame | frame in frames :: frame.Valid();
    //     assert rd.reader.data[endHeaderPos..rd.reader.pos] == MessageBody.FramesToSequence(frames);
    //   }
    //   assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]) by {
    //     assert endHeaderPos == |deserializeHeaderResult.hbSeq| + |header.auth.iv + header.auth.authenticationTag|;
    //     assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]);
    //   }
    //   assert FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]);
    // }

    // ghost var signature: Option<seq<uint8>> := None;
    // ghost var endFramePos := rd.reader.pos;
    // assert header.body.contentType.Framed? ==> 0 <= endHeaderPos <= endFramePos <= |request.message|;
    // if suite.signature.ECDSA? {
    //   var verifyResult, locSig := VerifySignature(rd, decMat);
    //   signature := Some(locSig);
    //   if verifyResult.Failure? {
    //     return Failure(verifyResult.error);
    //   }
    //   assert SignatureBySequence(signature.value, rd.reader.data[endFramePos..rd.reader.pos]); // Read signature from the sequence
    // }

    var signature :- VerifySignature(
      messageBody.tail,
      messageBody.tail.bytes[buffer.start..messageBody.tail.start],
      decMat
    );

    :- Need(signature.start == |signature.bytes|, "Data after message footer.");

    // var isDone := rd.IsDoneReading();
    // :- Need(isDone, "message contains additional bytes at end");

    // // Combine gathered facts and convert to postcondition
    // if header.body.contentType.Framed? {
    //   if suite.signature.ECDSA? { // Case with Signature
    //     assert signature.Some?;
    //     assert SignatureBySequence(signature.value, rd.reader.data[endFramePos..rd.reader.pos]);
    //     assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos])
    //       && FramesBySequence(frames, request.message[endHeaderPos..endFramePos])
    //       && SignatureBySequence(signature.value, request.message[endFramePos..]) by {
    //         assert 0 <= endHeaderPos <= endFramePos <= |request.message|;
    //         assert SignatureBySequence(signature.value, request.message[endFramePos..]) by {
    //         assert header.body.contentType.Framed? ==> SignatureBySequence(signature.value, rd.reader.data[endFramePos..rd.reader.pos]);
    //         assert rd.reader.data[endFramePos..rd.reader.pos] == request.message[endFramePos..] by {
    //           calc {
    //             rd.reader.data[endFramePos..rd.reader.pos];
    //           == {UpperBoundRemv(rd.reader.data, endFramePos); assert rd.reader.pos == |rd.reader.data|; }
    //             rd.reader.data[endFramePos..];
    //           == {assert rd.reader.data == request.message; }
    //             request.message[endFramePos..];
    //           }
    //         }
    //         assert SignatureBySequence(signature.value, rd.reader.data[endFramePos..rd.reader.pos]);
    //       }
    //     }
    //     HBandMBwithSigMatchSequence(header, deserializeHeaderResult.hbSeq, frames, signature.value, request.message);
    //   } else { // Case without signature
    //     assert signature.None?;
    //     assert 0 <= endHeaderPos <= |request.message| by {
    //       assert request.message == rd.reader.data;
    //     }
    //     assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos])
    //       && FramesBySequence(frames, request.message[endHeaderPos..]) by {
    //         assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos])
    //           && FramesBySequence(frames, rd.reader.data[endHeaderPos..rd.reader.pos]);
    //         assert rd.reader.data[endHeaderPos..rd.reader.pos] == request.message[endHeaderPos..] by {
    //           calc {
    //             rd.reader.data[endHeaderPos..rd.reader.pos];
    //           == {UpperBoundRemv(rd.reader.data, endHeaderPos); }
    //             rd.reader.data[endHeaderPos..];
    //           == {assert rd.reader.data == request.message; }
    //             request.message[endHeaderPos..];
    //           }
    //         }
    //       }
    //     assert 0 <= endHeaderPos <= |request.message|;
    //     HBandMBMatchSequence(header, deserializeHeaderResult.hbSeq, frames, request.message);
    //   }
    // }
    // var decryptResultWithVerificationInfo := DecryptResultWithVerificationInfo(plaintext, header, deserializeHeaderResult.hbSeq, frames, signature);
    // ghost var d := decryptResultWithVerificationInfo;
    // assert d.header.body.Valid();
    // assert Msg.IsSerializationOfHeaderBody(d.hbSeq, d.header.body);
    // if d.header.body.contentType.Framed? {
    //   assert forall frame: MessageBody.Frame | frame in d.frames :: frame.Valid();
    //   assert MessageBody.FramesEncryptPlaintext(d.frames, d.plaintext);
    //   assert match d.signature {
    //            case Some(_) =>
    //              && |d.signature.value| < UINT16_LIMIT
    //              && request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag // These items can be serialized to the output
    //                + MessageBody.FramesToSequence(d.frames) + UInt16ToSeq(|d.signature.value| as uint16) + d.signature.value
    //            case None => // if the result does not need to be signed
    //              request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag + MessageBody.FramesToSequence(d.frames)
    //          } by
    //   {
    //     if d.signature.Some? {
    //       assert |d.signature.value| < UINT16_LIMIT;
    //       assert request.message ==
    //                d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag // These items can be serialized to the output
    //                + MessageBody.FramesToSequence(d.frames) + UInt16ToSeq(|d.signature.value| as uint16) + d.signature.value;
    //     } else {
    //       assert request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag + MessageBody.FramesToSequence(d.frames);
    //     }
    //   }
    // }
    return Success(plaintext);
  }

  method VerifySignature(
    buffer: SerializeFunctions.ReadableBuffer,
    msg: seq<uint8>,
    decMat: Crypto.DecryptionMaterials
  )
    returns (res: Result<SerializeFunctions.ReadableBuffer, string>)
    // requires
    //   && messageStart.data == messageFooterStart.data
    //   && messageStart.start < messageFooterStart.start < |messageFooterStart.data|
    requires Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat)
    // requires rd.Valid()
    // requires Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.ECDSA?
    // requires decMat.verificationKey.Some?
    // modifies rd.reader`pos
    // ensures rd.Valid()

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
      .MapFailure(MapSerializeFailure);

    // var ecdsaParams := Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.curve;
    // var usedCapacity := rd.GetSizeRead();
    // assert usedCapacity == rd.reader.pos;
    // var msg := rd.reader.data[..usedCapacity];  // unauthenticatedHeader + authTag + body
    // // read signature
    // var signatureLengthResult := rd.ReadUInt16();
    // if signatureLengthResult.Failure? {
    //   return Failure(signatureLengthResult.error), [];
    // }
    // var sigResult := rd.ReadBytes(signatureLengthResult.value as nat);
    // if sigResult.Failure? {
    //   return Failure(sigResult.error), [];
    // }

    var ecdsaParams := Client.SpecificationClient().GetSuite(decMat.algorithmSuiteId).signature.curve;
    // verify signature
    var signatureVerifiedResult :- Signature.Verify(ecdsaParams, decMat.verificationKey.value, msg, signature.data);

    // if signatureVerifiedResult.Failure? {
    //   return Failure(signatureVerifiedResult.error), [];
    // }
    // if !signatureVerifiedResult.value {
    //   return Failure("signature not verified"), [];
    // }

    // assert SignatureBySequence(sigResult.value, rd.reader.data[old(rd.reader.pos)..rd.reader.pos]) by {
    //   reveal SignatureBySequence();
    // }
    return Success(signature.tail);
  }

  // predicate {:opaque } HeaderBySequence(header: Msg.Header, hbSeq: seq<uint8>, sequence: seq<uint8>)
  // {
  //   && header.body.contentType.Framed?
  //   && header.body.Valid()
  //   && Msg.IsSerializationOfHeaderBody(hbSeq, header.body)
  //   && sequence == hbSeq + header.auth.iv + header.auth.authenticationTag
  // }

  // predicate {:opaque } FramesBySequence(frames: seq<MessageBody.Frame>, sequence: seq<uint8>)
  // {
  //   && |frames| < UINT32_LIMIT
  //   && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid())
  //   && sequence == MessageBody.FramesToSequence(frames)
  // }

  predicate {:opaque } SignatureBySequence(signature: seq<uint8>, sequence: seq<uint8>)
  {
    && |signature| < UINT16_LIMIT
    && sequence == UInt16ToSeq(|signature| as uint16) + signature
  }

  // lemma HBandMBMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, message: seq<uint8>)
  //   requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
  //   requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag|
  //   requires exists headerLength | 0 <= headerLength <= |message| ::
  //     && HeaderBySequence(header, hbSeq, message[..headerLength])
  //     && FramesBySequence(frames, message[headerLength..])
  //   ensures message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames);
  // {
  //   reveal HeaderBySequence(), FramesBySequence();
  // }

  // lemma HBandMBwithSigMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, signature: seq<uint8>, message: seq<uint8>)
  //   requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
  //   requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag| + |MessageBody.FramesToSequence(frames)|
  //   requires exists headerLength, frameLength | 0 <= headerLength <= frameLength < |message| ::
  //     && HeaderBySequence(header, hbSeq, message[..headerLength])
  //     && FramesBySequence(frames, message[headerLength..frameLength])
  //     && SignatureBySequence(signature, message[frameLength..])
  //   ensures |signature| < UINT16_LIMIT &&
  //     message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames) + UInt16ToSeq(|signature| as uint16) + signature;
  // {
  //   reveal HeaderBySequence(), FramesBySequence(), SignatureBySequence();
  // }

  lemma UpperBoundRemv(sequence: seq<uint8>, lo: int)
    requires 0 <= lo <= |sequence|
    ensures sequence[lo..|sequence|] == sequence[lo..]
  {

  }

  // predicate DataIsFramed(sequence: seq<uint8>)
  // {
  //   exists i, header, hbSeq | 0 <= i <= |sequence| :: HeaderBySequence(header, hbSeq, sequence[..i])
  // }

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

  function method MapSerializeFailure(e: SerializeFunctions.ReadProblems): string {
    match e
      case Error(e) => e
      case MoreNeeded(_) => "Incomplete message"
  }

}
