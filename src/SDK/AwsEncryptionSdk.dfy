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
        const maxEncryptedDataKeys: Option<int64>;

        const client := new Client.AwsCryptographicMaterialProvidersClient();

        constructor (config: Esdk.AwsEncryptionSdkClientConfig)
            ensures this.config == config

            ensures config.commitmentPolicy.None? ==>
              && var policy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
              && this.commitmentPolicy == policy

            ensures config.commitmentPolicy.Some? ==>
                this.commitmentPolicy == config.commitmentPolicy.value

            ensures this.maxEncryptedDataKeys == config.maxEncryptedDataKeys
        {
            this.config := config;

            // TODO: Ideally we would validate that this value, if provided, falls within a specific range,
            // then only pass around known good values to all places where it is used.
            // However, currently Polymorph doesn't handle this smoothly for these service client
            // constructors and their configurations.
            this.maxEncryptedDataKeys := config.maxEncryptedDataKeys;

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

            // TODO: Change to '> 0' once CrypTool-4350 complete
            // TODO: Remove entirely once we can validate this value on client creation
            if this.maxEncryptedDataKeys.Some? {
                :- Need(this.maxEncryptedDataKeys.value >= 0, "maxEncryptedDataKeys must be non-negative");
            }

            var cmm :- CreateCmmFromInput(input.materialsManager, input.keyring);

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
            //# If the number of
            //# encrypted data keys (../framework/structures.md#encrypted-data-keys)
            //# on the encryption materials (../framework/structures.md#encryption-
            //# materials) is greater than the maximum number of encrypted data keys
            //# (client.md#maximum-number-of-encrypted-data-keys) configured in the
            //# client (client.md) encrypt MUST yield an error.
            var _ :- ValidateMaxEncryptedDataKeys(materials.encryptedDataKeys);

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

            var suite := Client.SpecificationClient().GetSuite(materials.algorithmSuiteId);
            var messageId: HeaderTypes.MessageId :- GenerateMessageId(suite);

            var maybeDerivedDataKeys := KeyDerivation.DeriveKeys(
                messageId, materials.plaintextDataKey.value, suite
            );
            :- Need(maybeDerivedDataKeys.Success?, "Failed to derive data keys");
            var derivedDataKeys := maybeDerivedDataKeys.value;

            var maybeHeader := BuildHeader(
                messageId,
                suite,
                materials.encryptionContext,
                encryptedDataKeys,
                frameLength as uint32,
                derivedDataKeys
            );

            :- Need(maybeHeader.Success?, "Failed to build header body");
            var header := maybeHeader.value;

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
         * Helper method for taking optional input keyrings/CMMs and returning a CMM,
         * either directly the one that was provided or a new default CMM from the
         * provided keyring.
         */
        method CreateCmmFromInput(
            inputCmm: Option<Crypto.ICryptographicMaterialsManager>,
            inputKeyring: Option<Crypto.IKeyring>
        ) returns (res: Result<Crypto.ICryptographicMaterialsManager, string>)

        //= compliance/client-apis/encrypt.txt#2.6.1
        //= type=implication
        //# The
        //# CMM used MUST be the input CMM, if supplied.

        //= compliance/client-apis/decrypt.txt#2.7.2
        //= type=implication
        //# The CMM used MUST be the input CMM, if supplied.
        ensures
            && res.Success?
            && inputCmm.Some?
        ==>
            res.value == inputCmm.value

        ensures
            && inputCmm.Some?
            && inputKeyring.Some?
        ==>
            res.Failure?

        ensures
            && inputCmm.None?
            && inputKeyring.None?
        ==>
            res.Failure?

        {
            :- Need(inputCmm.None? || inputKeyring.None?, "Cannot provide both a keyring and a CMM");
            :- Need(inputCmm.Some? || inputKeyring.Some?, "Must provide either a keyring or a CMM");

            var cmm : Crypto.ICryptographicMaterialsManager;
            if inputCmm.Some? {
                return Success(inputCmm.value);
            } else {
                // Each of these three citations refer to creating a default CMM from
                // the input keyring.

                //= compliance/client-apis/encrypt.txt#2.6.1
                //# If instead the caller
                //# supplied a keyring (../framework/keyring-interface.md), this behavior
                //# MUST use a default CMM (../framework/default-cmm.md) constructed
                //# using the caller-supplied keyring as input.

                //= compliance/client-apis/decrypt.txt#2.5.3
                //# If the Keyring is provided as the input, the client MUST construct a
                //# default CMM (../framework/default-cmm.md) that uses this keyring, to
                //# obtain the decryption materials (../framework/
                //# structures.md#decryption-materials) that is required for decryption.

                //= compliance/client-apis/decrypt.txt#2.7.2
                //# If a CMM is not
                //# supplied as the input, the decrypt operation MUST construct a default
                //# CMM (../framework/default-cmm.md) from the input keyring
                //# (../framework/keyring-interface.md).
                var createCmmOutput := this.client
                    .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
                    keyring := inputKeyring.value
                ));
                :- Need (createCmmOutput.Success?, "Failed to create default CMM");
                return Success(createCmmOutput.value);
            }
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
        ) returns (res: HeaderTypes.HeaderBody)

        requires suite.commitment.HKDF? ==>
            && suiteData.Some?
            && |suiteData.value| == suite.commitment.outputKeyLength as int

        // This ensures that our header is internally consistent with respect to
        // commitment (e.g. creating the right header version for the given suite)
        ensures Header.HeaderVersionSupportsCommitment?(suite, res)

        // Correct construction of V2 headers
        ensures
            && suite.commitment.HKDF?
        ==>
            && var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
            && res == HeaderTypes.HeaderBody.V2HeaderBody(
                esdkSuiteId := esdkAlgorithmSuiteId,
                messageId := messageId,
                encryptionContext := encryptionContext,
                encryptedDataKeys := encryptedDataKeys,
                contentType := HeaderTypes.ContentType.Framed,
                frameLength := frameLength,
                suiteData := suiteData.value
            )

        // Correct construction of V1 headers
        ensures
            && suite.commitment.None?
        ==>
            && var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);
            && res == HeaderTypes.HeaderBody.V1HeaderBody(
                messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
                esdkSuiteId := esdkAlgorithmSuiteId,
                messageId := messageId,
                encryptionContext := encryptionContext,
                encryptedDataKeys := encryptedDataKeys,
                contentType := HeaderTypes.ContentType.Framed,
                headerIvLength := suite.encrypt.ivLength as nat,
                frameLength := frameLength
            )
        {
            var esdkAlgorithmSuiteId := SerializableTypes.GetESDKAlgorithmSuiteId(suite.id);

            match suite.commitment {
                case None => return HeaderTypes.HeaderBody.V1HeaderBody(
                    messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := HeaderTypes.ContentType.Framed,
                    headerIvLength := suite.encrypt.ivLength as nat,
                    frameLength := frameLength
                );
                case HKDF => return HeaderTypes.HeaderBody.V2HeaderBody(
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := HeaderTypes.ContentType.Framed,
                    frameLength := frameLength,
                    suiteData := suiteData.value
                );
            }
        }

        method BuildHeaderAuthTag(
            suite: Client.AlgorithmSuites.AlgorithmSuite,
            dataKey: seq<uint8>,
            rawHeader: seq<uint8>
        )
            returns (res: Result<HeaderTypes.HeaderAuth, string>)

            ensures res.Success? ==> Header.HeaderAuth?(suite, res.value)
        {
            var keyLength := suite.encrypt.keyLength as int;
            :- Need(|dataKey| == keyLength, "Incorrect data key length");

            var ivLength := suite.encrypt.ivLength as int;
            var iv: seq<uint8> := seq(ivLength, _ => 0);

            var encryptionOutput :- AESEncryption.AESEncrypt(
                suite.encrypt,
                iv,
                dataKey,
                [],
                rawHeader
            );
            var headerAuth := HeaderTypes.HeaderAuth.AESMac(
                headerIv := iv,
                headerAuthTag := encryptionOutput.authTag
            );
            return Success(headerAuth);
        }

        method BuildHeader(
            messageId: HeaderTypes.MessageId,
            suite: Client.AlgorithmSuites.AlgorithmSuite,
            encryptionContext: Crypto.EncryptionContext,
            encryptedDataKeys: SerializableTypes.ESDKEncryptedDataKeys,
            frameLength: uint32,
            derivedDataKeys: KeyDerivation.ExpandedKeyMaterial
        ) returns (res: Result<Header.HeaderInfo, string>)

        requires SerializableTypes.IsESDKEncryptionContext(encryptionContext)

        requires suite.commitment.HKDF? ==>
            && derivedDataKeys.commitmentKey.Some?
            && |derivedDataKeys.commitmentKey.value| == suite.commitment.outputKeyLength as int

        // TODO: may need changing when we need to support non-framed
        requires frameLength > 0

        // Make sure the output correctly uses the values that were given as input
        ensures res.Success? ==>
            && res.value.suite == suite
            && res.value.body.frameLength == frameLength
            && res.value.encryptionContext == encryptionContext

        ensures res.Success? ==> Header.IsHeader(res.value)

        // TODO: change when we need to support non-framed
        ensures res.Success? ==> res.value.body.contentType.Framed?
        {
            var canonicalEncryptionContext := EncryptionContext.GetCanonicalEncryptionContext(encryptionContext);

            var body := BuildHeaderBody(
                messageId,
                suite,
                canonicalEncryptionContext,
                encryptedDataKeys,
                frameLength as uint32,
                derivedDataKeys.commitmentKey
            );

            var rawHeader := Header.WriteHeaderBody(body);

            var headerAuth :- BuildHeaderAuthTag(suite, derivedDataKeys.dataKey, rawHeader);

            var header := Header.HeaderInfo(
                body := body,
                rawHeader := rawHeader,
                encryptionContext := encryptionContext,
                suite := suite,
                headerAuth := headerAuth
            );

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

            return Success(header);
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
            // TODO: Change to '> 0' once CrypTool-4350 complete
            // TODO: Remove entirely once we can validate this value on client creation
            if this.maxEncryptedDataKeys.Some? {
                :- Need(this.maxEncryptedDataKeys.value >= 0, "maxEncryptedDataKeys must be non-negative");
            }

            var cmm :- CreateCmmFromInput(input.materialsManager, input.keyring);

            var buffer := SerializeFunctions.ReadableBuffer(input.ciphertext, 0);
            var headerBody :- Header
                .ReadHeaderBody(buffer, this.maxEncryptedDataKeys)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadHeaderBody"));

            var rawHeader := headerBody.tail.bytes[buffer.start..headerBody.tail.start];

            var algorithmSuiteId := SerializableTypes.GetAlgorithmSuiteId(headerBody.data.esdkSuiteId);
            var _ := Client.SpecificationClient().ValidateCommitmentPolicyOnDecrypt(
                algorithmSuiteId, this.commitmentPolicy
            );

            var decMat :- GetDecryptionMaterials(cmm, algorithmSuiteId, headerBody.data);

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

            :- Need(Header.HeaderVersionSupportsCommitment?(suite, headerBody.data), "Invalid commitment values found in header body");
            if suite.commitment.HKDF? {
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
            assert {:split_here} true;

            // TODO: add support for non-framed content
            :- Need(headerBody.data.contentType.Framed?, "Fix me");

            var header := Header.HeaderInfo(
                body := headerBody.data,
                rawHeader := rawHeader,
                encryptionContext := decMat.encryptionContext,
                suite := suite,
                headerAuth := headerAuth.data
            );

            // TODO: The below assertions were added to give hints to the verifier in order to speed
            // up verification. They can almost certainly be refactored into something prettier.
            :- Need(
                SerializableTypes.GetESDKAlgorithmSuiteId(header.suite.id) == header.body.esdkSuiteId,
                "Invalid header: algorithm suite mismatch"
            );
            :- Need(header.body.contentType.Framed?, "Non-framed messages not supported");
            :- Need(header.body.frameLength > 0, "Non-framed messages not supported");
            
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

        method GetDecryptionMaterials(
            cmm: Crypto.ICryptographicMaterialsManager,
            algorithmSuiteId: Crypto.AlgorithmSuiteId,
            headerBody: HeaderTypes.HeaderBody
        ) returns (res: Result<Crypto.DecryptionMaterials, string>)

        ensures res.Success? ==> Client.Materials.DecryptionMaterialsWithPlaintextDataKey(res.value)

        ensures res.Success? ==> SerializableTypes.IsESDKEncryptionContext(res.value.encryptionContext)
        {
            var encryptionContext := EncryptionContext.GetEncryptionContext(headerBody.encryptionContext);

            var decMatRequest := Crypto.DecryptMaterialsInput(
                algorithmSuiteId:=algorithmSuiteId,
                commitmentPolicy:=this.commitmentPolicy,
                encryptedDataKeys:=headerBody.encryptedDataKeys,
                encryptionContext:=encryptionContext
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

            :- Need(SerializableTypes.IsESDKEncryptionContext(decMat.encryptionContext), "CMM failed to return serializable encryption materials.");

            return Success(decMat);
        }

        method ValidateMaxEncryptedDataKeys(edks: SerializableTypes.ESDKEncryptedDataKeys)
            returns (res: Result<(), string>)

        // TODO: change to '> 0' once CrypTool-4350 fixed
        requires this.maxEncryptedDataKeys.Some? ==> this.maxEncryptedDataKeys.value >= 0

        ensures this.maxEncryptedDataKeys.None? ==> res.Success?

        ensures
            && this.maxEncryptedDataKeys.Some?
            && this.maxEncryptedDataKeys.value > 0 // TODO: remove once CrypTool-4350 fixed
            && |edks| as int64 > this.maxEncryptedDataKeys.value
        ==>
            res.Failure?
        {
            if
                && this.maxEncryptedDataKeys.Some?
                && this.maxEncryptedDataKeys.value > 0 // TODO: remove once CrypTool-4350 fixed
                && |edks| as int64 > this.maxEncryptedDataKeys.value
            {
                return Failure("Encrypted data keys exceed maxEncryptedDataKeys");
            } else {
                return Success(());
            }
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
    ) returns (res: Result<(), string>)

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

        return Success(());
    }
}
