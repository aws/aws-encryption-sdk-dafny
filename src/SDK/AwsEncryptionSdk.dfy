// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// TODO: Originally written as part of POC; we should come back through this
// to refine it

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Util/UTF8.dfy"
include "../AwsCryptographicMaterialProviders/Client.dfy"
include "../Crypto/Random.dfy"
include "../Crypto/AESEncryption.dfy"
include "EncryptDecrypt.dfy"
include "KeyDerivation.dfy"
include "ConfigDefaults.dfy"

include "Serialize/SerializableTypes.dfy"
include "Serialize/Header.dfy"
include "Serialize/HeaderTypes.dfy"
include "Serialize/V1HeaderBody.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/SerializeFunctions.dfy"
include "Serialize/EncryptionContext.dfy"

module {:extern "Dafny.Aws.Esdk.AwsEncryptionSdkClient"} AwsEncryptionSdk {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Aws.Crypto
  import Aws.Esdk
  import EncryptDecryptHelpers
  import KeyDerivation
  import SerializableTypes
  import Random
  import MaterialProviders.Client
  import AESEncryption
  import EncryptionContext
  import SerializeFunctions
  import MessageBody
  import Signature
  import ConfigDefaults

  import Header
  import HeaderTypes
  import HeaderAuth
  import V1HeaderBody

  class AwsEncryptionSdkClient extends Esdk.IAwsEncryptionSdkClient {
        const config: Esdk.AwsEncryptionSdkClientConfig;

        const commitmentPolicy: Crypto.CommitmentPolicy;

        constructor (config: Esdk.AwsEncryptionSdkClientConfig)
            ensures this.config == config

            ensures config.commitmentPolicy.None? ==>
              && var policy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
              && this.commitmentPolicy == policy

            ensures config.commitmentPolicy.Some? ==>
                this.commitmentPolicy == config.commitmentPolicy.value
        {
            this.config := config;
            if config.commitmentPolicy.None? {
                var defaultPolicy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
                this.commitmentPolicy := defaultPolicy;
            } else {
                this.commitmentPolicy := config.commitmentPolicy.value;
            }
        }

        // Doing this conversion at each error site would allow us to emit more specific error types.
        // But we don't have specific error types right now,
        // and to use them,
        // we'd have to instantiate errors within their own statements since they need to be allocated via `new`.
        // This is tedious and obscures the already-long business logic.
        //
        // We can safely refactor this at a later date to use more specific error types,
        // because errors are abstracted by the common error trait.
        // So for expedience, we put the business logic in an internal method,
        // and provide this facade that wraps any failure message inside the generic error type.
        method Encrypt(input: Esdk.EncryptInput)
            returns (res: Result<Esdk.EncryptOutput, Esdk.IAwsEncryptionSdkException>)
        {
            var encryptResult := EncryptInternal(input);
            var withConvertedError := Esdk.AwsEncryptionSdkClientException.WrapResultString(encryptResult);
            return withConvertedError;
        }

        method EncryptInternal(input: Esdk.EncryptInput) returns (res: Result<Esdk.EncryptOutput, string>)
        //= compliance/client-apis/encrypt.txt#2.6.1
        //= type=implication
        //# If an input algorithm suite (Section 2.4.5) is provided that is not
        //# supported by the commitment policy (client.md#commitment-policy)
        //# configured in the client (client.md) encrypt MUST yield an error.
        ensures
        (
            && input.algorithmSuiteId.Some?
            && var valid := Client.SpecificationClient()
                    .ValidateCommitmentPolicyOnEncrypt(input.algorithmSuiteId.value, this.commitmentPolicy);
            && valid.Failure?
        )
        ==>
            res.Failure?
        {
            // Validate encrypt request
            // TODO: bring back once we can have Option<Trait>
            //:- Need(request.cmm != null || request.keyring != null, "EncryptRequest.cmm OR EncryptRequest.keyring must be set.");
            //:- Need(!(request.cmm != null && request.keyring != null), "EncryptRequest.keyring AND EncryptRequest.cmm must not both be set.");
            var frameLength : int64 := EncryptDecryptHelpers.DEFAULT_FRAME_LENGTH;
            if input.frameLength.Some? {
                // TODO: uncomment this once we figure out why C# is passing 0 as the default value for these nullable
                // fields
                //frameLength := request.frameLength.value;
            }
            :- Need(frameLength > 0, "Requested frame length must be > 0");

            var maxPlaintextLength := INT64_MAX_LIMIT - 1;
            if input.maxPlaintextLength.Some? {
                // TODO: uncomment this once we figure out why C# is passing 0 as the default value for these nullable
                // fields
                //maxPlaintextLength := request.maxPlaintextLength.value;
            }
            :- Need(maxPlaintextLength < INT64_MAX_LIMIT, "Input plaintext size too large.");


            var cmm := input.materialsManager;
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

            var algorithmSuiteId := input.algorithmSuiteId;

            if algorithmSuiteId.Some? {
                var _ :- Client.SpecificationClient()
                    .ValidateCommitmentPolicyOnEncrypt(algorithmSuiteId.value, this.commitmentPolicy);
            }

            var materials :- GetEncryptionMaterials(
                cmm,
                algorithmSuiteId,
                input.encryptionContext,
                maxPlaintextLength as int64
            );

            //= compliance/client-apis/encrypt.txt#2.6.1
            //# If this
            //# algorithm suite (../framework/algorithm-suites.md) is not supported
            //# by the commitment policy (client.md#commitment-policy) configured in
            //# the client (client.md) encrypt MUST yield an error.
            var algorithmAllowed := Client.SpecificationClient()
                    .ValidateCommitmentPolicyOnEncrypt(materials.algorithmSuiteId, this.commitmentPolicy);
            :- Need(
                algorithmAllowed.Success?,
                "CMM return algorithm suite not supported by our commitment policy"
            );
            var encryptedDataKeys: SerializableTypes.ESDKEncryptedDataKeys := materials.encryptedDataKeys;

            var canonicalEncryptionContext := EncryptionContext.GetCanonicalEncryptionContext(materials.encryptionContext);

            var suite := Client.SpecificationClient().GetSuite(materials.algorithmSuiteId);
            var messageId: HeaderTypes.MessageId :- GenerateMessageId(suite);

            var maybeDerivedDataKeys := KeyDerivation.DeriveKeys(
                messageId, materials.plaintextDataKey.value, suite
            );
            :- Need(maybeDerivedDataKeys.Success?, "Failed to derive data keys");
            var derivedDataKeys := maybeDerivedDataKeys.value;

            if suite.messageVersion == 2 {
                :- Need(derivedDataKeys.commitmentKey.Some?, "Message version 2 requires suite data");
            }

            var maybeBody := BuildHeaderBody(
                messageId,
                suite,
                canonicalEncryptionContext,
                encryptedDataKeys,
                frameLength as uint32,
                derivedDataKeys.commitmentKey
            );

            :- Need(maybeBody.Success?, "Failed to build header body");

            var body := maybeBody.value;
            assert false;

            var rawHeader := Header.WriteHeaderBody(body);
            assert false;

            var iv: seq<uint8> := seq(suite.encrypt.ivLength as int, _ => 0);
            var encryptionOutput :- AESEncryption.AESEncrypt(
                suite.encrypt,
                iv,
                derivedDataKeys.dataKey,
                [],
                rawHeader
            );
            var headerAuth := HeaderTypes.HeaderAuth.AESMac(
                headerIv := iv,
                headerAuthTag := encryptionOutput.authTag
            );

            var header := Header.HeaderInfo(
                body := body,
                rawHeader := rawHeader,
                encryptionContext := materials.encryptionContext,
                suite := suite,
                headerAuth := headerAuth
            );
            assert false;

            // Add headerAuth requirements to Header type
            assert Header.CorrectlyReadHeaderBody(
                SerializeFunctions.ReadableBuffer(rawHeader, 0),
                Success(
                    SerializeFunctions.SuccessfulRead(
                        body,
                        SerializeFunctions.ReadableBuffer(rawHeader, |rawHeader|)
                    )
                )
            );
            assert Header.HeaderAuth?(suite, headerAuth);
            assert Header.IsHeader(header);

            // Encrypt the given plaintext into the framed message
            var framedMessage :- MessageBody.EncryptMessageBody(
                input.plaintext,
                header,
                derivedDataKeys.dataKey
            );

            if framedMessage.finalFrame.header.suite.signature.ECDSA? {
                var msg :- EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage, suite);
                var ecdsaParams := framedMessage.finalFrame.header.suite.signature.curve;
                // TODO: This should just work, but Proof is difficult
                :- Need(materials.signingKey.Some?, "Missing signing key.");

                var bytes :- Signature.Sign(ecdsaParams, materials.signingKey.value, msg);
                :- Need(|bytes| == ecdsaParams.SignatureLength() as int, "Malformed response from Sign().");

                var signature := UInt16ToSeq(|bytes| as uint16) + bytes;
                msg := msg + signature;
                // TODO: Come back and prove this
                // assert msg == SerializeMessageWithSignature(framedMessage, signature); // Header, frames and signature can be serialized into the stream
            return Success(Esdk.EncryptOutput(ciphertext := msg));
            } else {
                var msg :- EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage, suite);
                return Success(Esdk.EncryptOutput(ciphertext := msg));
            }
        }

        method GetEncryptionMaterials(
            cmm: Crypto.ICryptographicMaterialsManager,
            algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>,
            encryptionContext: Crypto.EncryptionContext,
            maxPlaintextLength: int64
        ) returns (res: Result<Crypto.EncryptionMaterials, string>)

        ensures res.Success? ==>
            && Client.Materials.EncryptionMaterialsWithPlaintextDataKey(res.value)

        ensures res.Success? ==>
            && SerializableTypes.IsESDKEncryptionContext(res.value.encryptionContext)
        
        ensures res.Success? ==>
            && HasUint16Len(res.value.encryptedDataKeys)

        ensures res.Success? ==>
            && forall edk | edk in res.value.encryptedDataKeys
                :: SerializableTypes.IsESDKEncryptedDataKey(edk)
        {
            var encMatRequest := Crypto.GetEncryptionMaterialsInput(
                encryptionContext:=encryptionContext,
                commitmentPolicy:=this.commitmentPolicy,
                algorithmSuiteId:=algorithmSuiteId,
                maxPlaintextLength:=Option.Some(maxPlaintextLength)
            );

            var getEncMatResult := cmm.GetEncryptionMaterials(encMatRequest);
            var output :- match getEncMatResult {
                case Success(value) => Success(value)
                case Failure(exception) => Failure(exception.GetMessage())
            };

            var materials := output.encryptionMaterials;

            // Validations to ensure we got back materials that we can use
            :- Need(
                Client.Materials.EncryptionMaterialsWithPlaintextDataKey(materials),
                "CMM returned invalid EncryptionMaterials"
            );
            :- Need(
                SerializableTypes.IsESDKEncryptionContext(materials.encryptionContext),
                "CMM failed to return serializable encryption materials."
            );
            :- Need(HasUint16Len(materials.encryptedDataKeys), "CMM returned EDKs that exceed the allowed maximum.");
            :- Need(forall edk | edk in materials.encryptedDataKeys
                :: SerializableTypes.IsESDKEncryptedDataKey(edk),
                "CMM returned non-serializable encrypted data key.");

            return Success(materials);
        }

        /*
         * Generate a message id of appropriate length for the given algorithm suite.
         */
        method GenerateMessageId(
            suite: Client.AlgorithmSuites.AlgorithmSuite
        ) returns (res: Result<HeaderTypes.MessageId, string>)

        ensures
            && res.Success?
            && suite.messageVersion == 1
        ==>
            |res.value| == HeaderTypes.MESSAGE_ID_LEN_V1

        ensures
            && res.Success?
            && suite.messageVersion == 2
        ==>
            |res.value| == HeaderTypes.MESSAGE_ID_LEN_V2
        {
            var id;
            if suite.messageVersion == 1 {
                id :- Random.GenerateBytes(HeaderTypes.MESSAGE_ID_LEN_V1 as int32);
            } else {
                id :- Random.GenerateBytes(HeaderTypes.MESSAGE_ID_LEN_V2 as int32);
            }

            return Success(id);
        }

        method BuildHeaderBody(
            messageId: HeaderTypes.MessageId,
            suite: Client.AlgorithmSuites.AlgorithmSuite,
            encryptionContext: EncryptionContext.ESDKCanonicalEncryptionContext,
            encryptedDataKeys: SerializableTypes.ESDKEncryptedDataKeys,
            frameLength: uint32,
            suiteData: Option<seq<uint8>>
        ) returns (res: Result<HeaderTypes.HeaderBody, string>)

        requires suite.messageVersion == 2 ==> suiteData.Some?

        // Correct construction of V2 headers
        ensures
            && res.Success?
            && suite.messageVersion == 2
        ==>
            && res.value.V2HeaderBody?
            && var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
            && res.value == HeaderTypes.HeaderBody.V2HeaderBody(
                esdkSuiteId := esdkAlgorithmSuiteId,
                messageId := messageId,
                encryptionContext := encryptionContext,
                encryptedDataKeys := encryptedDataKeys,
                contentType := HeaderTypes.ContentType.Framed, // TODO: may need to change to support non-framed
                frameLength := frameLength,
                suiteData := suiteData.value
            )

        // Correct construction of V1 headers
        ensures
            && res.Success?
            && suite.messageVersion == 1
        ==>
            && res.value.V1HeaderBody?
            && var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
            && res.value == HeaderTypes.HeaderBody.V1HeaderBody(
                messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
                esdkSuiteId := esdkAlgorithmSuiteId,
                messageId := messageId,
                encryptionContext := encryptionContext,
                encryptedDataKeys := encryptedDataKeys,
                contentType := HeaderTypes.ContentType.Framed, // TODO: may need to change to support non-framed
                headerIvLength := suite.encrypt.ivLength as nat,
                frameLength := frameLength
            )

        /* TODO: Including this makes verification time balloon. Why?
        ensures
        (
            && suite.messageVersion != 1
            && suite.messageVersion != 2
        )
        ==>
            res.Failure?
        */
        {
            var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);

            match suite.messageVersion {
                case 1 => return Success(HeaderTypes.HeaderBody.V1HeaderBody(
                    messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := HeaderTypes.ContentType.Framed,
                    headerIvLength := suite.encrypt.ivLength as nat,
                    frameLength := frameLength
                ));
                case 2 => return Success(HeaderTypes.HeaderBody.V2HeaderBody(
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := HeaderTypes.ContentType.Framed,
                    frameLength := frameLength,
                    suiteData := suiteData.value
                ));
                case _ => return Failure("");
            }
        }

        // See Encrypt/EncryptInternal for an explanation of why we separate Decrypt and DecryptInternal.
        method Decrypt(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, Esdk.IAwsEncryptionSdkException>)
        {
            var decryptResult := DecryptInternal(input);
            var withConvertedError := Esdk.AwsEncryptionSdkClientException.WrapResultString(decryptResult);
            return withConvertedError;
        }

        method DecryptInternal(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, string>)
        {
            // Validate decrypt request
            // TODO: bring back once we can have Option<Trait>
            //:- Need(request.cmm == null || request.keyring == null, "DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both).");
            //:- Need(request.cmm != null || request.keyring != null, "DecryptRequest.cmm and DecryptRequest.keyring cannot both be null.");

            var cmm := input.materialsManager;
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

            var buffer := SerializeFunctions.ReadableBuffer(input.ciphertext, 0);
            var headerBody :- Header
                .ReadHeaderBody(buffer)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadHeaderBody"));

            var rawHeader := headerBody.tail.bytes[buffer.start..headerBody.tail.start];

            var esdkEncryptionContext := EncryptionContext.GetEncryptionContext(headerBody.data.encryptionContext);

            var algorithmSuiteId := SerializableTypes.GetAlgorithmSuiteId(headerBody.data.esdkSuiteId);
            var _ := Client.SpecificationClient().ValidateCommitmentPolicyOnDecrypt(
                algorithmSuiteId, this.commitmentPolicy
            );

            var decMatRequest := Crypto.DecryptMaterialsInput(
                algorithmSuiteId:=algorithmSuiteId,
                commitmentPolicy:=this.commitmentPolicy,
                encryptedDataKeys:=headerBody.data.encryptedDataKeys,
                encryptionContext:=esdkEncryptionContext
            );
            var decMatResult := cmm.DecryptMaterials(decMatRequest);
            var output :- match decMatResult {
                case Success(value) => Success(value)
                case Failure(exception) => Failure(exception.GetMessage())
            };
            var decMat := output.decryptionMaterials;

            // Validate decryption materials
            :- Need(
                Client.Materials.DecryptionMaterialsWithPlaintextDataKey(decMat),
                "CMM returned invalid DecryptMaterials"
            );

            var suite := Client
                .SpecificationClient()
                .GetSuite(decMat.algorithmSuiteId);

            var headerAuth :- HeaderAuth
                .ReadHeaderAuthTag(headerBody.tail, suite)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadHeaderAuthTag"));

            var maybeDerivedDataKeys := KeyDerivation.DeriveKeys(
                headerBody.data.messageId, decMat.plaintextDataKey.value, suite
            );
            :- Need(maybeDerivedDataKeys.Success?, "Failed to derive data keys");
            var derivedDataKeys := maybeDerivedDataKeys.value;

            if suite.messageVersion == 2 {
                :- Need(derivedDataKeys.commitmentKey.Some?, "Algorithm has commitment but suite data not present");
                var _ :- ValidateSuiteData(suite, headerBody.data, derivedDataKeys.commitmentKey.value);
            }

            // We created the header auth tag by encrypting an
            // empty array. To verify it here, we don't care about the actual
            // result of the decryption, just that it succeeds, hence the
            // anonymous variable name.
            var _ :- AESEncryption.AESDecrypt(
                suite.encrypt,
                derivedDataKeys.dataKey,
                [],
                headerAuth.data.headerAuthTag,
                headerAuth.data.headerIv,
                rawHeader
            );

            // TODO: add support for non-framed content
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
            SerializeFunctions.ReadableBuffer(rawHeader, 0),
            Success(
                SerializeFunctions.SuccessfulRead(
                    headerBody.data, SerializeFunctions.ReadableBuffer(rawHeader, |rawHeader|))
                )
            );
            assert Header.HeaderAuth?(suite, headerAuth.data);
            assert Header.IsHeader(header);

            var messageBody :- MessageBody.ReadFramedMessageBody(
                headerAuth.tail,
                header,
                [],
                headerAuth.tail
            ).MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadFramedMessageBody"));

            assert {:split_here} true;
            assert suite == messageBody.data.finalFrame.header.suite;
            assert |derivedDataKeys.dataKey| == messageBody.data.finalFrame.header.suite.encrypt.keyLength as int;

            // ghost var endHeaderPos := rd.reader.pos;
            // Parse the message body
            var plaintext;
            match header.body.contentType {
                case NonFramed => return Failure("not at this time");
                //   plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, suite, decryptionKey, header.body.messageID);
                case Framed =>
                    plaintext :- MessageBody.DecryptFramedMessageBody(messageBody.data, derivedDataKeys.dataKey);
            }

            var signature :- EncryptDecryptHelpers.VerifySignature(
                messageBody.tail,
                messageBody.tail.bytes[buffer.start..messageBody.tail.start],
                decMat
            );

            :- Need(signature.start == |signature.bytes|, "Data after message footer.");

            return Success(Esdk.DecryptOutput(plaintext := plaintext));
        }
    }

    /*
     * Ensures that the suite data contained in the header of a message matches
     * the expected suite data
     */
    method ValidateSuiteData(
        suite: Client.AlgorithmSuites.AlgorithmSuite,
        header: HeaderTypes.HeaderBody,
        expectedSuiteData: seq<uint8>
    ) returns (res: Result<bool, string>)

    // Validating suite data is only relevant for suites with commitment
    requires suite.commitment.HKDF?

    // We can't dereference the 'suiteData' portion of the body, which only exists
    // in V2 headers, unless we know we have a V2HeaderBody
    requires header.V2HeaderBody?

    // Happy case
    ensures res.Success? ==> header.suiteData == expectedSuiteData
    
    // Failure cases
    ensures header.suiteData != expectedSuiteData ==> res.Failure?
    ensures |header.suiteData| != suite.commitment.outputKeyLength as int ==> res.Failure?
    {
        :- Need(|header.suiteData| == suite.commitment.outputKeyLength as int, "Commitment key is invalid");
        :- Need(expectedSuiteData == header.suiteData, "Commitment key does not match");

        return Success(true);
    }
}
