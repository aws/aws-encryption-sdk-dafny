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
include "Serialize/Frames.dfy"
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
  import Frames

  class AwsEncryptionSdkClient extends Esdk.IAwsEncryptionSdkClient {
        const config: Esdk.AwsEncryptionSdkClientConfig;

        //= compliance/client-apis/client.txt#2.4
        //= type=implication
        //# Once a commitment policy (Section 2.4.1) has been set it SHOULD be
        //# immutable.
        const commitmentPolicy: Crypto.CommitmentPolicy;
        const maxEncryptedDataKeys: Option<int64>;

        const materialProvidersClient: Crypto.IAwsCryptographicMaterialsProviderClient;

        //= compliance/client-apis/client.txt#2.4
        //= type=implication
        //# On client initialization, the caller MUST have the option to provide
        //# a:
        //#*  commitment policy (Section 2.4.1)
        //#*  maximum number of encrypted data keys (Section 2.4.2)
        constructor (config: Esdk.AwsEncryptionSdkClientConfig)
            ensures this.config == config

            //= compliance/client-apis/client.txt#2.4
            //= type=implication
            //# If no commitment policy (Section 2.4.1) is provided the default MUST
            //# be REQUIRE_ENCRYPT_REQUIRE_DECRYPT (../framework/algorithm-
            //# suites.md#require_encrypt_require_decrypt).
            ensures config.commitmentPolicy.None? ==>
              && var policy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
              && this.commitmentPolicy == policy

            ensures config.commitmentPolicy.Some? ==>
                this.commitmentPolicy == config.commitmentPolicy.value

            //= compliance/client-apis/client.txt#2.4
            //# If no maximum number of
            //# encrypted data keys (Section 2.4.2) is provided the default MUST
            //# result in no limit on the number of encrypted data keys (aside from
            //# the limit imposed by the message format (../format/message-
            //# header.md)).
            // This is a citation, not an implication, as setting the maxEDK as an option
            // does not enforce the specified behavior at all.
            //= compliance/client-apis/client.txt#2.4.2
            //= type=implication
            //# Callers MUST have a way to disable
            //# this limit.
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

            this.materialProvidersClient := new Client.AwsCryptographicMaterialProvidersClient();
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
                // TODO: uncomment once https://issues.amazon.com/issues/CrypTool-4350 fixed

                //= compliance/client-apis/encrypt.txt#2.4.6
                //= type=TODO
                //# This value
                //# MUST be greater than 0 and MUST NOT exceed the value 2^32 - 1.
                //frameLength := request.frameLength.value;
            }
            :- Need(frameLength > 0, "Requested frame length must be > 0");

            var maxPlaintextLength := INT64_MAX_LIMIT - 1;
            if input.maxPlaintextLength.Some? {
                // TODO: uncomment once https://issues.amazon.com/issues/CrypTool-4350 fixed
                //maxPlaintextLength := request.maxPlaintextLength.value;
            }
            :- Need(maxPlaintextLength < INT64_MAX_LIMIT, "Input plaintext size too large.");

            // TODO: Change to '> 0' once CrypTool-4350 complete
            // TODO: Remove entirely once we can validate this value on client creation
            if this.maxEncryptedDataKeys.Some? {
                :- Need(this.maxEncryptedDataKeys.value >= 0, "maxEncryptedDataKeys must be non-negative");
            }

            var cmm :- CreateCmmFromInput(input.materialsManager, input.keyring);

            //= compliance/client-apis/encrypt.txt#2.4.5
            //# The algorithm suite (../framework/algorithm-suite.md) that SHOULD be
            //# used for encryption.
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

            //= compliance/client-apis/encrypt.txt#2.6.1
            //# The algorithm suite (../framework/algorithm-suites.md) used in all
            //# aspects of this operation MUST be the algorithm suite in the
            //# encryption materials (../framework/structures.md#encryption-
            //# materials) returned from the Get Encryption Materials (../framework/
            //# cmm-interface.md#get-encryption-materials) call.
            var suite := Client.SpecificationClient().GetSuite(materials.algorithmSuiteId);
            var messageId: HeaderTypes.MessageId :- GenerateMessageId(suite);

            var maybeDerivedDataKeys := KeyDerivation.DeriveKeys(
                messageId, materials.plaintextDataKey.value, suite
            );
            :- Need(maybeDerivedDataKeys.Success?, "Failed to derive data keys");
            var derivedDataKeys := maybeDerivedDataKeys.value;

            var maybeHeader := BuildHeaderForEncrypt(
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
                //= compliance/client-apis/encrypt.txt#2.7.2
                //# If the algorithm suite (../framework/algorithm-suites.md) contains a
                //# signature algorithm (../framework/algorithm-suites.md#signature-
                //# algorithm), this operation MUST calculate a signature over the
                //# message, and the output encrypted message (Section 2.5.1) MUST
                //# contain a message footer (../data-format/message-footer.md).

                //= compliance/client-apis/encrypt.txt#2.6
                //# If the encryption materials gathered (Section 2.6.1) has a
                //# algorithm suite including a signature algorithm (../framework/
                //# algorithm-suites.md#signature-algorithm), the encrypt operation
                //# MUST perform this step.

                var msg :- EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage, suite);
                var ecdsaParams := framedMessage.finalFrame.header.suite.signature.curve;
                // TODO: This should just work, but Proof is difficult
                :- Need(materials.signingKey.Some?, "Missing signing key.");

                //= compliance/client-apis/encrypt.txt#2.7.2
                //# To calculate a signature, this operation MUST use the signature
                //# algorithm (../framework/algorithm-suites.md#signature-algorithm)
                //# specified by the algorithm suite (../framework/algorithm-suites.md),
                //# with the following input:
                //#*  the signature key is the signing key (../framework/
                //#   structures.md#signing-key) in the encryption materials
                //#   (../framework/structures.md#encryption-materials)
                //#*  the input to sign is the concatenation of the serialization of the
                //#   message header (../data-format/message-header.md) and message body
                //#   (../data-format/message-body.md)
                var bytes :- Signature.Sign(ecdsaParams, materials.signingKey.value, msg);
                :- Need(|bytes| == ecdsaParams.SignatureLength() as int, "Malformed response from Sign().");

                //= compliance/client-apis/encrypt.txt#2.7.2
                //# This operation MUST then serialize a message footer with the
                //# following specifics:

                //= compliance/client-apis/encrypt.txt#2.7.2
                //# *  Signature Length (../data-format/message-footer.md#signature-
                //# length): MUST be the length of the output of the calculation
                //# above.

                //= compliance/client-apis/encrypt.txt#2.7.2
                //# *  Signature (../data-format/message-footer.md#signature): MUST be
                //# the output of the calculation above.
                var signature := UInt16ToSeq(|bytes| as uint16) + bytes;

                //= compliance/client-apis/encrypt.txt#2.7.2
                //# The encrypted message output by this operation MUST have a message
                //# footer equal to the message footer calculated in this step.
                msg := msg + signature;
                // TODO: Come back and prove this
                // assert msg == SerializeMessageWithSignature(framedMessage, signature); // Header, frames and signature can be serialized into the stream

                //= compliance/client-apis/encrypt.txt#2.5
                //# This behavior MUST output the following if the behavior is
                //# successful:
                //# *  Encrypted Message (Section 2.5.1)
                //# *  Encryption Context (Section 2.4.2)
                //# *  Algorithm Suite (Section 2.4.5)
                return Success(
                    Esdk.EncryptOutput(
                        ciphertext := msg,
                        encryptionContext := header.encryptionContext,
                        algorithmSuiteId := header.suite.id
                    )
                );
            } else {
                //= compliance/client-apis/encrypt.txt#2.6
                //# Otherwise the encrypt operation MUST
                //# NOT perform this step.
                var msg :- EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage, suite);
                return Success(
                    Esdk.EncryptOutput(
                        ciphertext := msg,
                        encryptionContext := header.encryptionContext,
                        algorithmSuiteId := header.suite.id
                    )
                );
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

            //= compliance/client-apis/encrypt.txt#2.6.1
            //# This operation MUST obtain this set of encryption
            //# materials (../framework/structures.md#encryption-materials) by
            //# calling Get Encryption Materials (../framework/cmm-interface.md#get-
            //# encryption-materials) on a CMM (../framework/cmm-interface.md).
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
                var createCmmOutput := this.materialProvidersClient
                    .CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
                        keyring := inputKeyring.value
                    )
                );
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

        //= compliance/data-format/message-header.txt#2.5.2
        //= type=implication
        //# The length of the suite data field MUST be equal to
        //# the Algorithm Suite Data Length (../framework/algorithm-
        //# suites.md#algorithm-suite-data-length) value of the algorithm suite
        //# (../framework/algorithm-suites.md) specified by the Algorithm Suite
        //# ID (Section 2.5.1.5) field.
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

            //= compliance/client-apis/encrypt.txt#2.8.1
            //# Implementations of the AWS Encryption SDK MUST NOT encrypt using the
            //# Non-Framed content type.
            var contentType := HeaderTypes.ContentType.Framed;

            match suite.commitment {
                case None => return HeaderTypes.HeaderBody.V1HeaderBody(
                    messageType := HeaderTypes.MessageType.TYPE_CUSTOMER_AED,
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := contentType,
                    headerIvLength := suite.encrypt.ivLength as nat,
                    frameLength := frameLength
                );
                case HKDF => return HeaderTypes.HeaderBody.V2HeaderBody(
                    esdkSuiteId := esdkAlgorithmSuiteId,
                    messageId := messageId,
                    encryptionContext := encryptionContext,
                    encryptedDataKeys := encryptedDataKeys,
                    contentType := contentType,
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
            //= compliance/client-apis/encrypt.txt#2.6.2
            //# The
            //# value of this MUST be the output of the authenticated encryption
            //# algorithm (../framework/algorithm-suites.md#encryption-algorithm)
            //# specified by the algorithm suite (../framework/algorithm-suites.md),
            //# with the following inputs:
            var keyLength := suite.encrypt.keyLength as int;
            :- Need(|dataKey| == keyLength, "Incorrect data key length");

            var ivLength := suite.encrypt.ivLength as int;
            //#*  The IV has a value of 0.
            var iv: seq<uint8> := seq(ivLength, _ => 0);

            var encryptionOutput :- AESEncryption.AESEncrypt(
                suite.encrypt,
                iv,
                //#*  The cipherkey is the derived data key
                dataKey,
                //#*  The plaintext is an empty byte array
                [],
                //#*  The AAD is the serialized message header body (../data-format/
                //#   message-header.md#header-body).
                rawHeader
            );
            var headerAuth := HeaderTypes.HeaderAuth.AESMac(
                headerIv := iv,
                headerAuthTag := encryptionOutput.authTag
            );
            return Success(headerAuth);
        }

        // We restrict this method to the encrypt path so that we can assume the body is framed.
        method BuildHeaderForEncrypt(
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

        requires frameLength > 0

        // Make sure the output correctly uses the values that were given as input
        ensures res.Success? ==>
            && res.value.suite == suite
            && res.value.body.frameLength == frameLength
            && res.value.encryptionContext == encryptionContext

        ensures res.Success? ==> Header.IsHeader(res.value)

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

            //= compliance/client-apis/encrypt.txt#2.6.2
            //# Before encrypting input plaintext, this operation MUST serialize the
            //# message header body (../data-format/message-header.md).
            var rawHeader := Header.WriteHeaderBody(body);

            //= compliance/client-apis/encrypt.txt#2.6.2
            //# After serializing the message header body, this operation MUST
            //# calculate an authentication tag (../data-format/message-
            //# header.md#authentication-tag) over the message header body.
            var headerAuth :- BuildHeaderAuthTag(suite, derivedDataKeys.dataKey, rawHeader);

            var header := Header.HeaderInfo(
                body := body,
                rawHeader := rawHeader,
                encryptionContext := encryptionContext,
                suite := suite,
                headerAuth := headerAuth
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

        method DecryptInternal(input: Esdk.DecryptInput)
            returns (res: Result<Esdk.DecryptOutput, string>)

        //= compliance/client-apis/decrypt.txt#2.7.2
        //= type=implication
        //# If the parsed algorithm suite ID (../data-format/message-
        //# header.md#algorithm-suite-id) is not supported by the commitment
        //# policy (client.md#commitment-policy) configured in the client
        //# (client.md) decrypt MUST yield an error.
        ensures
        (
            && var buffer := SerializeFunctions.ReadableBuffer(input.ciphertext, 0);
            && var headerBody := Header.ReadHeaderBody(buffer, this.maxEncryptedDataKeys);
            && headerBody.Success?
            && var algorithmSuiteId := SerializableTypes.GetAlgorithmSuiteId(headerBody.value.data.esdkSuiteId);
            && Client.SpecificationClient().ValidateCommitmentPolicyOnDecrypt(
                algorithmSuiteId, this.commitmentPolicy
            ).Failure?
        )
        ==>
            res.Failure?

        //= compliance/client-apis/decrypt.txt#2.6
        //= type=implication
        //# The client MUST return as output to this operation:
        ensures res.Success?
        ==>
            && var buffer := SerializeFunctions.ReadableBuffer(input.ciphertext, 0);
            && var headerBody := Header.ReadHeaderBody(buffer, this.maxEncryptedDataKeys);
            && headerBody.Success?
            // *  Algorithm Suite (Section 2.6.3)
            && var algorithmSuiteId := SerializableTypes.GetAlgorithmSuiteId(headerBody.value.data.esdkSuiteId);
            && res.value.algorithmSuiteId == algorithmSuiteId
            // *  Encryption Context (Section 2.6.2)
            && var ec := EncryptionContext.GetEncryptionContext(headerBody.value.data.encryptionContext);
            && res.value.encryptionContext == ec

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
            var _ :- Client.SpecificationClient().ValidateCommitmentPolicyOnDecrypt(
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

            var receivedEncryptionContext := EncryptionContext.GetEncryptionContext(
                headerBody.data.encryptionContext
            );
            :- Need(
                SerializableTypes.IsESDKEncryptionContext(receivedEncryptionContext),
                "Received invalid encryption context"
            );

            var header := Header.HeaderInfo(
                body := headerBody.data,
                rawHeader := rawHeader,
                encryptionContext := receivedEncryptionContext,
                suite := suite,
                headerAuth := headerAuth.data
            );

            // TODO: The below assertions were added to give hints to the verifier in order to speed
            // up verification. They can almost certainly be refactored into something prettier.
            :- Need(
                SerializableTypes.GetESDKAlgorithmSuiteId(header.suite.id) == header.body.esdkSuiteId,
                "Invalid header: algorithm suite mismatch"
            );

            assert {:split_here} true;

            assert Header.HeaderAuth?(suite, headerAuth.data);
            assert Header.IsHeader(header);

            var key := derivedDataKeys.dataKey;
            var plaintext: seq<uint8>;
            var messageBodyTail: SerializeFunctions.ReadableBuffer;
            match header.body.contentType {
                case NonFramed =>
                    var decryptRes :- ReadAndDecryptNonFramedMessageBody(headerAuth.tail, header, key);
                    plaintext := decryptRes.0;
                    messageBodyTail := decryptRes.1;
                case Framed =>
                    var decryptRes :- ReadAndDecryptFramedMessageBody(headerAuth.tail, header, key);
                    plaintext := decryptRes.0;
                    messageBodyTail := decryptRes.1;
            }

            assert {:split_here} true;

            var signature :- EncryptDecryptHelpers.VerifySignature(
                messageBodyTail,
                messageBodyTail.bytes[buffer.start..messageBodyTail.start],
                decMat
            );

            :- Need(signature.start == |signature.bytes|, "Data after message footer.");

            return Success(
                Esdk.DecryptOutput(
                    plaintext := plaintext,
                    encryptionContext := header.encryptionContext,
                    algorithmSuiteId := header.suite.id
                )
            );
        }

        method ReadAndDecryptFramedMessageBody(
            buffer: SerializeFunctions.ReadableBuffer,
            header: Frames.FramedHeader,
            key: seq<uint8>
        )
            returns (res: Result<(seq<uint8>, SerializeFunctions.ReadableBuffer), string>)
            requires buffer.start <= |buffer.bytes|
            requires |key| == header.suite.encrypt.keyLength as int
            ensures res.Success? ==>
                var (plaintext, tail) := res.value;
                && SerializeFunctions.CorrectlyReadRange(buffer, tail)
        {
            assert SerializeFunctions.CorrectlyReadRange(buffer, buffer);
            var messageBody :- MessageBody.ReadFramedMessageBody(buffer, header, [], buffer)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadFramedMessageBody"));

            assert header == messageBody.data.finalFrame.header;
            assert |key| == messageBody.data.finalFrame.header.suite.encrypt.keyLength as int;
            var plaintext :- MessageBody.DecryptFramedMessageBody(messageBody.data, key);
            var messageBodyTail := messageBody.tail;

            return Success((plaintext, messageBodyTail));
        }

        method ReadAndDecryptNonFramedMessageBody(
            buffer: SerializeFunctions.ReadableBuffer,
            header: Frames.NonFramedHeader,
            key: seq<uint8>
        )
            returns (res: Result<(seq<uint8>, SerializeFunctions.ReadableBuffer), string>)
            requires buffer.start <= |buffer.bytes|
            requires |key| == header.suite.encrypt.keyLength as int
            ensures res.Success? ==>
                var (plaintext, tail) := res.value;
                && SerializeFunctions.CorrectlyReadRange(buffer, tail)
        {
            var messageBody :- MessageBody.ReadNonFramedMessageBody(buffer, header)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadNonFramedMessageBody"));
            var frame: Frames.Frame := messageBody.data;
            assert frame.NonFramed?;

            assert header == frame.header;
            assert |key| == frame.header.suite.encrypt.keyLength as int;

            var plaintext :- MessageBody.DecryptFrame(frame, key);
            var messageBodyTail := messageBody.tail;
            return Success((plaintext, messageBodyTail));
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
