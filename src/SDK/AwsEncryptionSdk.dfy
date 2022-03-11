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

include "Serialize/SerializableTypes.dfy"
include "Serialize/Header.dfy"
include "Serialize/HeaderTypes.dfy"
include "Serialize/V1HeaderBody.dfy"
include "Serialize/HeaderAuth.dfy"
include "Serialize/Frames.dfy"
include "Serialize/SerializeFunctions.dfy"
include "Serialize/EncryptionContext.dfy"

module {:extern "Dafny.Aws.Esdk.AwsEncryptionSdk"} AwsEncryptionSdk {
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

  import Header
  import HeaderTypes
  import HeaderAuth
  import V1HeaderBody
  import Frames

  type FrameLength = frameLength : int64 | 0 < frameLength <= 0xFFFF_FFFF witness *
  
  const DEFAULT_COMMITMENT_POLICY : Crypto.CommitmentPolicy := Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;

  class AwsEncryptionSdk extends Esdk.IAwsEncryptionSdk {
        const config: Esdk.AwsEncryptionSdkConfig;

        //= compliance/client-apis/client.txt#2.4
        //= type=implication
        //# Once a commitment policy (Section 2.4.1) has been set it SHOULD be
        //# immutable.
        const commitmentPolicy: Crypto.CommitmentPolicy;
        const maxEncryptedDataKeys: Option<int64>;

        const materialProviders: Crypto.IAwsCryptographicMaterialProviders;

        const RESERVED_ENCRYPTION_CONTEXT := UTF8.Encode("aws-crypto-").value;

        //= compliance/client-apis/client.txt#2.4
        //= type=implication
        //# On client initialization, the caller MUST have the option to provide
        //# a:
        //#*  commitment policy (Section 2.4.1)
        //#*  maximum number of encrypted data keys (Section 2.4.2)

        constructor (config: Esdk.AwsEncryptionSdkConfig)
            ensures this.config == config

            //= compliance/client-apis/client.txt#2.4
            //= type=implication
            //# If no commitment policy (Section 2.4.1) is provided the default MUST
            //# be REQUIRE_ENCRYPT_REQUIRE_DECRYPT (../framework/algorithm-
            //# suites.md#require_encrypt_require_decrypt).
            ensures config.commitmentPolicy.None? ==>
              && this.commitmentPolicy == DEFAULT_COMMITMENT_POLICY

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

            this.maxEncryptedDataKeys := config.maxEncryptedDataKeys;

            if config.commitmentPolicy.None? {
                this.commitmentPolicy := DEFAULT_COMMITMENT_POLICY;
            } else {
                this.commitmentPolicy := config.commitmentPolicy.value;
            }

            this.materialProviders := new Client.AwsCryptographicMaterialProviders();
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
            var withConvertedError := Esdk.AwsEncryptionSdkException.WrapResultString(encryptResult);
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

       //= compliance/client-apis/encrypt.txt#2.4.6
       //= type=implication
       //# This value
       //# MUST be greater than 0 and MUST NOT exceed the value 2^32 - 1. 
        ensures
            && input.frameLength.Some?
            && (input.frameLength.value <= 0 || input.frameLength.value > 0xFFFF_FFFF)
        ==>
            res.Failure?            
        {
            var frameLength : FrameLength := EncryptDecryptHelpers.DEFAULT_FRAME_LENGTH;
            if input.frameLength.Some? {
              :- Need(
                0 < input.frameLength.value <= 0xFFFF_FFFF,
                "FrameLength must be greater than 0 and less than 2^32"
              );
              frameLength := input.frameLength.value;
            }

            // TODO: Remove entirely once we can validate this value on client creation
            if this.maxEncryptedDataKeys.Some? {
                :- Need(this.maxEncryptedDataKeys.value > 0, "maxEncryptedDataKeys must be positive");
            }

            if input.encryptionContext.Some? {
                var _ :- ValidateEncryptionContext(input.encryptionContext.value);
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

            // int64 fits 9 exabytes so we're never going to actually hit this. But if we don't
            // include this the verifier is not convinced that we can cast the size to int64
            :- Need(|input.plaintext| < INT64_MAX_LIMIT, "Plaintext exceeds maximum allowed size");
            var materials :- GetEncryptionMaterials(
                cmm,
                algorithmSuiteId,
                input.encryptionContext,
                //= compliance/client-apis/encrypt.txt#2.6.1
                //# *  Max Plaintext Length: If the input plaintext (Section 2.4.1) has
                //# known length, this length MUST be used.
                |input.plaintext| as int64
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

                //= compliance/data-format/message-footer.txt#2.3
                //# When an algorithm suite (../framework/algorithm-suites.md) includes a
                //# signature algorithm (../framework/algorithm-suites.md#signature-
                //# algorithm), the message (message.md) MUST contain a footer.

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
            inputEncryptionContext: Option<Crypto.EncryptionContext>,
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
            var encryptionContext : Crypto.EncryptionContext;
            if inputEncryptionContext.Some? {
                encryptionContext := inputEncryptionContext.value;
            } else {
                encryptionContext := map[];
            }

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
                var createCmmOutput := this.materialProviders
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
            var withConvertedError := Esdk.AwsEncryptionSdkException.WrapResultString(decryptResult);
            return withConvertedError;
        }

        method DecryptInternal(input: Esdk.DecryptInput)
            returns (res: Result<Esdk.DecryptOutput, string>)

        //= compliance/client-apis/decrypt.txt#2.7
        //= type=TODO
        //# This operation MUST perform all the above steps unless otherwise
        //# specified, and it MUST perform them in the above order.

        //= compliance/client-apis/decrypt.txt#2.7.2
        //= type=implication
        //# If the parsed algorithm suite ID (../data-format/message-
        //# header.md#algorithm-suite-id) is not supported by the commitment
        //# policy (client.md#commitment-policy) configured in the client
        //# (client.md) decrypt MUST yield an error.

        //= compliance/client-apis/decrypt.txt#2.7.2
        //= type=implication
        //# If the
        //# algorithm suite is not supported by the commitment policy
        //# (client.md#commitment-policy) configured in the client (client.md)
        //# decrypt MUST yield an error.
        // TODO :: Consider removing from spec as this is redundent
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

        //= compliance/client-apis/decrypt.txt#2.5
        //= type=implication
        //# The client MUST require exactly one of the following types of inputs:
        //#*  Cryptographic Materials Manager (CMM) (../framework/cmm-
        //#   interface.md)
        //#*  Keyring (../framework/keyring-interface.md)
        ensures
        (
          || (input.materialsManager.Some? && input.keyring.Some?)
          || (input.materialsManager.None? && input.keyring.None?)
        )
        ==>  
          res.Failure?

        {
            // TODO: Remove entirely once we can validate this value on client creation
            if this.maxEncryptedDataKeys.Some? {
                :- Need(this.maxEncryptedDataKeys.value > 0, "maxEncryptedDataKeys must be positive");
            }

            var cmm :- CreateCmmFromInput(input.materialsManager, input.keyring);

            //= compliance/client-apis/decrypt.txt#2.7.1
            //# Given encrypted message bytes, this operation MUST process those
            //# bytes sequentially, deserializing those bytes according to the
            //# message format (../data-format/message.md).

            var buffer := SerializeFunctions.ReadableBuffer(input.ciphertext, 0);

            //= compliance/client-apis/decrypt.txt#2.5.1.1
            //= type=TODO
            //# To make diagnosing this mistake easier, implementations SHOULD detect
            //# the first two bytes of the Base64 encoding of any supported message
            //# versions (../data-format/message-header.md#version-1) and types
            //# (../data-format/message-header.md#type) and fail with a more specific
            //# error message.

            var headerBody :- Header
                .ReadHeaderBody(buffer, this.maxEncryptedDataKeys)
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadHeaderBody"));

            var rawHeader := headerBody.tail.bytes[buffer.start..headerBody.tail.start];

            var algorithmSuiteId := SerializableTypes.GetAlgorithmSuiteId(headerBody.data.esdkSuiteId);
            //= compliance/client-apis/decrypt.txt#2.7.2
            //# If the
            //# algorithm suite is not supported by the commitment policy
            //# (client.md#commitment-policy) configured in the client (client.md)
            //# decrypt MUST yield an error.
            var _ :- Client.SpecificationClient().ValidateCommitmentPolicyOnDecrypt(
                algorithmSuiteId, this.commitmentPolicy
            );

            //= compliance/client-apis/decrypt.txt#2.5.2
            //# This CMM MUST obtain the decryption materials (../framework/
            //# structures.md#decryption-materials) required for decryption.

            //= compliance/client-apis/decrypt.txt#2.5.3
            //# This default CMM MUST obtain the decryption materials required for
            //# decryption.
            // TODO :: Consider removing "Default CMM MUST obtain" from spec.
            // It is redundent and hard to prove.

            //= compliance/client-apis/decrypt.txt#2.7.2
            //# This operation MUST obtain this set of decryption materials
            //# (../framework/structures.md#decryption-materials), by calling Decrypt
            //# Materials (../framework/cmm-interface.md#decrypt-materials) on a CMM
            //# (../framework/cmm-interface.md).
            var decMat :- GetDecryptionMaterials(cmm, algorithmSuiteId, headerBody.data);

            var suite := Client
                .SpecificationClient()
                .GetSuite(decMat.algorithmSuiteId);

            //= compliance/client-apis/decrypt.txt#2.4.2
            //# This operation MUST NOT release any unauthenticated plaintext or
            //# unauthenticated associated data.
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

            //= compliance/client-apis/decrypt.txt#2.7.3
            //# If this tag verification fails, this operation MUST immediately halt
            //# and fail.
            var _ :-
              //= compliance/client-apis/decrypt.txt#2.7.3
              //# Once a valid message header is deserialized and decryption materials
              //# are available, this operation MUST validate the message header body
              //# (../data-format/message-header.md#header-body) by using the
              //# authenticated encryption algorithm (../framework/algorithm-
              //# suites.md#encryption-algorithm) to decrypt with the following inputs:
              AESEncryption.AESDecrypt(
                suite.encrypt,
                //#*  the cipherkey is the derived data key
                derivedDataKeys.dataKey,
                //#*  the ciphertext is an empty byte array
                [],
                //#*  the tag is the value serialized in the message header's
                //#   authentication tag field (../data-format/message-
                //#   header.md#authentication-tag)
                headerAuth.data.headerAuthTag,
                //#*  the IV is the value serialized in the message header's IV field
                //#   (../data-format/message-header#iv).
                headerAuth.data.headerIv,
                //#*  the AAD is the serialized message header body (../data-format/
                //#   message-header.md#header-body).
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

            //= compliance/client-apis/decrypt.txt#2.7.4
            //# Once the message header is successfully parsed, the next sequential
            //# bytes MUST be deserialized according to the message body spec
            //# (../data-format/message-body.md).
            
            //= compliance/client-apis/decrypt.txt#2.7.4
            //# The content type (../data-format/message-header.md#content-type)
            //# field parsed from the message header above determines whether these
            //# bytes MUST be deserialized as framed data (../data-format/message-
            //# body.md#framed-data) or un-framed data (../data-format/message-
            //# body.md#un-framed-data).
            match header.body.contentType {
                case NonFramed =>
                    //= compliance/client-apis/decrypt.txt#2.7.4
                    //# If this decryption fails, this operation MUST immediately halt and
                    //# fail.
                    var decryptRes :- ReadAndDecryptNonFramedMessageBody(headerAuth.tail, header, key);
                    plaintext := decryptRes.0;
                    messageBodyTail := decryptRes.1;
                    
                case Framed =>
                    //= compliance/client-apis/decrypt.txt#2.7.4
                    //# If this decryption fails, this operation MUST immediately halt and
                    //# fail.
                    var decryptRes :- ReadAndDecryptFramedMessageBody(headerAuth.tail, header, key);
                    plaintext := decryptRes.0;
                    messageBodyTail := decryptRes.1;
            }

            assert {:split_here} true;

            //= compliance/client-apis/decrypt.txt#2.7.5
            //# If this verification is not successful, this operation MUST
            //# immediately halt and fail.
            var signature :- EncryptDecryptHelpers.VerifySignature(
                messageBodyTail,
                messageBodyTail.bytes[buffer.start..messageBodyTail.start],
                decMat
            );

            :- Need(signature.start == |signature.bytes|, "Data after message footer.");

            //= compliance/client-apis/decrypt.txt#2.7.1
            //# Until the header is verified (Section 2.7.3), this operation MUST NOT
            //# release any parsed information from the header.
            // Note that the header is verified above

            //= compliance/client-apis/decrypt.txt#2.7.4
            //# This operation MUST NOT release any unauthenticated plaintext.

            //= compliance/client-apis/decrypt.txt#2.7
            //# If the input encrypted message is not being streamed (streaming.md)
            //# to this operation, all output MUST NOT be released until after these
            //# steps complete successfully.
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
            //= compliance/client-apis/decrypt.txt#2.7.2
            //# ./framework/cmm-
            //# interface.md#decrypt-materials) operation MUST be constructed as
            //# follows:
            var decMatRequest := Crypto.DecryptMaterialsInput(
                //#*  Algorithm Suite ID: This is the parsed algorithm suite ID
                //#   (../data-format/message-header.md#algorithm-suite-id) from the
                //#   message header.
                algorithmSuiteId:=algorithmSuiteId,
                commitmentPolicy:=this.commitmentPolicy,
                //#*  Encrypted Data Keys: This is the parsed encrypted data keys
                //#   (../data-format/message-header#encrypted-data-keys) from the
                //#   message header.
                encryptedDataKeys:=headerBody.encryptedDataKeys,
                //#*  Encryption Context: This is the parsed encryption context
                //#   (../data-format/message-header.md#aad) from the message header.
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

        /*
        * Ensures that an input encryption context does not contain any values
        * which use the reserved prefix
        */
        method ValidateEncryptionContext(input: Crypto.EncryptionContext)
            returns (res: Result<(), string>)
        //= compliance/client-apis/encrypt.txt#2.4.2
        //= type=implication
        //# The prefix "aws-crypto-" is reserved for internal use by the AWS
        //# Encryption SDK; see the the Default CMM spec (default-cmm.md) for one
        //# such use.
        //# If the input encryption context contains any entries with
        //# a key beginning with this prefix, the encryption operation MUST fail.
        ensures
            (exists key: UTF8.ValidUTF8Bytes | key in input.Keys :: RESERVED_ENCRYPTION_CONTEXT <= key)
        ==>
            res.Failure?
        {
            // In this method, we're looping through all keys and failing if any violate the reserved prefix.
            // Because we're using a loop, if we want to be able to prove things about what went on inside
            // the loop, we need a loop invariant. So our approach will be to track two sets of keys,
            // ones we have checked and ones we haven't checked; we can then set invariants on the loop
            // proving that all keys we've checked satisfy the constraint.

            ghost var checkedKeys: set<UTF8.ValidUTF8Bytes> := {};
            var uncheckedKeys: set<UTF8.ValidUTF8Bytes> := input.Keys;

            while uncheckedKeys != {}
                // Prove we'll terminate
                decreases |uncheckedKeys|
                // Prove we don't miss any keys
                invariant uncheckedKeys + checkedKeys == input.Keys
                // Prove that all checked keys satisfy our constraint
                invariant forall key | key in checkedKeys :: ! (RESERVED_ENCRYPTION_CONTEXT <= key)
            {
                var key :| key in uncheckedKeys;

                if RESERVED_ENCRYPTION_CONTEXT <= key {
                    return Failure("Encryption context keys cannot contain reserved prefix 'aws-crypto-'");
                }

                uncheckedKeys := uncheckedKeys - { key };
                checkedKeys := checkedKeys + {key};
            }
            return Success(());
        }

        method ValidateMaxEncryptedDataKeys(edks: SerializableTypes.ESDKEncryptedDataKeys)
            returns (res: Result<(), string>)

        requires this.maxEncryptedDataKeys.Some? ==> this.maxEncryptedDataKeys.value > 0

        ensures this.maxEncryptedDataKeys.None? ==> res.Success?

        ensures
            && this.maxEncryptedDataKeys.Some?
            && |edks| as int64 > this.maxEncryptedDataKeys.value
        ==>
            res.Failure?
        {
            if
                && this.maxEncryptedDataKeys.Some?
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

    //= compliance/client-apis/decrypt.txt#2.7.2
    //= type=implication
    //# The
    //# derived commit key MUST equal the commit key stored in the message
    //# header.
    ensures res.Success? ==> header.suiteData == expectedSuiteData

    // Failure cases
    ensures header.suiteData != expectedSuiteData ==> res.Failure?
    ensures |header.suiteData| != suite.commitment.outputKeyLength as int ==> res.Failure?
    {
      :- Need(
        |header.suiteData| == suite.commitment.outputKeyLength as int,
        "Commitment key is invalid"
      );

      :- Need(
        expectedSuiteData == header.suiteData,
        "Commitment key does not match"
      );

      return Success(());
    }
}
