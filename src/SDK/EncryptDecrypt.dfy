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
include "../Generated/AwsEncryptionSdk.dfy"
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
  import Aws.Esdk
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

  const DEFAULT_FRAME_LENGTH : int64 := 4096

  // Specification of Encrypt with signature
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

 /*
  * Encrypt a plaintext and serialize it into a message.
  */
  method Encrypt(request: Esdk.EncryptInput)
      returns (res: Result<Esdk.EncryptOutput, string>)

    // TODO: bring back once we can have Option<Trait>
    //ensures request.cmm == null && request.keyring == null ==> res.Failure?
    //ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.value == 0 ==> res.Failure?
  {
    // Validate encrypt request
    // TODO: bring back once we can have Option<Trait>
    //:- Need(request.cmm != null || request.keyring != null, "EncryptRequest.cmm OR EncryptRequest.keyring must be set.");
    //:- Need(!(request.cmm != null && request.keyring != null), "EncryptRequest.keyring AND EncryptRequest.cmm must not both be set.");
    var frameLength : int64 := DEFAULT_FRAME_LENGTH;
    if request.frameLength.Some? {
      // TODO: uncomment this once we figure out why C# is passing 0 as the default value for these nullable
      // fields
      //frameLength := request.frameLength.value;
    }
    :- Need(frameLength > 0, "Requested frame length must be > 0");

    var maxPlaintextLength := INT64_MAX_LIMIT - 1;
    if request.maxPlaintextLength.Some? {
      // TODO: uncomment this once we figure out why C# is passing 0 as the default value for these nullable
      // fields
      //maxPlaintextLength := request.maxPlaintextLength.value;
    }
    :- Need(maxPlaintextLength < INT64_MAX_LIMIT, "Input plaintext size too large.");


    var cmm := request.materialsManager;
    // TODO: bring back once we can have Option<Trait>
    /*
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      var client := new Client.AwsCryptographicMaterialProvidersClient();
      cmm := client
        .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
        keyring := request.keyring
      ));
    }*/

    var algorithmSuiteID := request.algorithmSuiteId;

    var encMatRequest := Crypto.GetEncryptionMaterialsInput(
      encryptionContext:=request.encryptionContext,
      algorithmSuiteId:=algorithmSuiteID,
      maxPlaintextLength:=Option.Some(maxPlaintextLength as int64)
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
      frameLength := frameLength as uint32
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
      return Success(Esdk.EncryptOutput(ciphertext := msg));
    } else {
      var msg := SerializeMessageWithoutSignature(framedMessage);
      return Success(Esdk.EncryptOutput(ciphertext := msg));
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

  // Verification of this method requires verification of the CMM to some extent, The verification of the Decrypt method should be extended after CMM is verified
  method Decrypt(request: Esdk.DecryptInput)
    returns (res: Result<Esdk.DecryptOutput, string>)
    // TODO: bring back once we can have Option<Trait>
    //ensures request.cmm == null && request.keyring == null ==> res.Failure?
    //ensures request.cmm != null && request.keyring != null ==> res.Failure?

  {
    // Validate decrypt request
    // TODO: bring back once we can have Option<Trait>
    //:- Need(request.cmm == null || request.keyring == null, "DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
    //:- Need(request.cmm != null || request.keyring != null, "DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");

    var cmm := request.materialsManager;
    // TODO: bring back once we can have Option<Trait>
    /*
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      var client := new Client.AwsCryptographicMaterialProvidersClient();
      cmm := client
        .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
        keyring := request.keyring
      ));
    }*/

    var buffer := SerializeFunctions.ReadableBuffer(request.ciphertext, 0);
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

    return Success(Esdk.DecryptOutput(plaintext := plaintext));
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
