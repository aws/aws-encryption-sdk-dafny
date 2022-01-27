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
        {
            this.config := config;
            if config.commitmentPolicy.None? {
                var defaultPolicy := ConfigDefaults.GetDefaultCommitmentPolicy(config.configDefaults);
                this.commitmentPolicy := defaultPolicy;
            } else {
                this.commitmentPolicy := config.commitmentPolicy.value;
            }
        }

        method Encrypt(input: Esdk.EncryptInput) returns (res: Result<Esdk.EncryptOutput, string>)
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

            var algorithmSuiteID := input.algorithmSuiteId;

            var encMatRequest := Crypto.GetEncryptionMaterialsInput(
                encryptionContext:=input.encryptionContext,
                commitmentPolicy:=this.commitmentPolicy,
                algorithmSuiteId:=algorithmSuiteID,
                maxPlaintextLength:=Option.Some(maxPlaintextLength as int64)
            );

            var output :- cmm.GetEncryptionMaterials(encMatRequest);

            var encMat := output.encryptionMaterials;

            // Validate encryption materials
            :- Need(
                Client.Materials.EncryptionMaterialsWithPlaintextDataKey(encMat),
                "CMM returned invalid EncryptionMaterials"
            );
            :- Need(
                SerializableTypes.IsESDKEncryptionContext(encMat.encryptionContext),
                "CMM failed to return serializable encryption materials."
            );
            :- Need(HasUint16Len(encMat.encryptedDataKeys), "CMM returned EDKs that exceed the allowed maximum.");
            :- Need(forall edk | edk in encMat.encryptedDataKeys
                :: SerializableTypes.IsESDKEncryptedDataKey(edk),
                "CMM returned non-serializable encrypted data key.");

            var encryptedDataKeys: SerializableTypes.ESDKEncryptedDataKeys := encMat.encryptedDataKeys;

            var esdkId := SerializableTypes.GetESDKAlgorithmSuiteId(encMat.algorithmSuiteId);
            var suite := Client.SpecificationClient().GetSuite(encMat.algorithmSuiteId);
            var messageID: HeaderTypes.MessageID :- Random.GenerateBytes(HeaderTypes.MESSAGE_ID_LEN as int32);
            var derivedDataKey := EncryptDecryptHelpers.DeriveKey(encMat.plaintextDataKey.value, suite, messageID);

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
                derivedDataKey
            );

            if framedMessage.finalFrame.header.suite.signature.ECDSA? {
                var msg := EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage);
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
                var msg := EncryptDecryptHelpers.SerializeMessageWithoutSignature(framedMessage);
                return Success(Esdk.EncryptOutput(ciphertext := msg));
            }
        }

        method Decrypt(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, string>)
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

            var decMatRequest := Crypto.DecryptMaterialsInput(
            algorithmSuiteId:=SerializableTypes.GetAlgorithmSuiteId(headerBody.data.esdkSuiteId),
            commitmentPolicy:=this.commitmentPolicy,
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
                .MapFailure(EncryptDecryptHelpers.MapSerializeFailure(": ReadAESMac"));

            var decryptionKey := EncryptDecryptHelpers.DeriveKey(decMat.plaintextDataKey.value, suite, headerBody.data.messageId);

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

            var signature :- EncryptDecryptHelpers.VerifySignature(
                messageBody.tail,
                messageBody.tail.bytes[buffer.start..messageBody.tail.start],
                decMat
            );

            :- Need(signature.start == |signature.bytes|, "Data after message footer.");

            return Success(Esdk.DecryptOutput(plaintext := plaintext));
        }
    }
}
