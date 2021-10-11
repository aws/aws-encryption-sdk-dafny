include "../../Util/UTF8.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/AmazonKeyManagementService.dfy"

module {:extern "CryptographicMaterialProviders"} CryptographicMaterialProviders {
    import opened Wrappers
    import AmazonKeyManagementService

    // TODO: KMS client will live here
    module KMS {
        import UTF8
        import AmazonKeyManagementService

        type KmsKeyId = string
        type KmsKeyIdList = seq<KmsKeyId>

        type GrantToken = string
        type GrantTokenList = seq<GrantToken>

        trait IClientSupplier {
            method GetClient(region: string) returns (res: AmazonKeyManagementService.IAmazonKeyManagementService)
        }
    }

    // TODO: don't necessarily need sub-structures here. Perhaps Dafny modules are 1:1 with
    // Smithy namespaces, in which case all of this lives under the "aws.crypto" module.
    // But for now it seems like a nice way of separating things out. Alternatively we could
    // update the Smithy model to have more sub-namespaces ("aws.crypto.structures").
    module Structures {
        import UTF8
        import opened UInt = StandardLibrary.UInt
        import opened Wrappers
        import CryptoConfig

        type EncryptionContext = map<string, string>

        datatype EncryptedDataKey = EncryptedDataKey(nameonly providerID: UTF8.ValidUTF8Bytes,
                                                     nameonly providerInfo: seq<uint8>,
                                                     nameonly ciphertext: seq<uint8>)
        {
            // TODO: constraints not currently modeled in Smithy
            predicate Valid() {
                |providerID| < UINT16_LIMIT &&
                |providerInfo| < UINT16_LIMIT &&
                |ciphertext| < UINT16_LIMIT
            }
        }
        type ValidEncryptedDataKey = i : EncryptedDataKey | i.Valid() witness *

        type EncryptedDataKeyList = seq<EncryptedDataKey>

        // There are a number of assertions we can make about materials to validate correctness
        // (for example: if the algorithm suite includes signing, signingKey must not be null).
        // However, we cannot model these in Smithy, so we will need to write them manually in the
        // Dafny code rather than in this auto-generated portion.
        datatype EncryptionMaterials = EncryptionMaterials(nameonly encryptionContext: Option<EncryptionContext>,
                                                           nameonly algorithm: Option<CryptoConfig.AlgorithmSuite>,
                                                           nameonly plaintextDataKey: Option<seq<uint8>>,
                                                           nameonly encryptedDataKeys: Option<seq<ValidEncryptedDataKey>>,
                                                           nameonly signingKey: Option<seq<uint8>>)

        datatype DecryptionMaterials = DecryptionMaterials(nameonly encryptionContext: Option<EncryptionContext>,
                                                           nameonly algorithm: Option<CryptoConfig.AlgorithmSuite>,
                                                           nameonly plaintextDataKey: Option<seq<uint8>>,
                                                           nameonly verificationKey: Option<seq<uint8>>)
    }

    module CryptoConfig {
        datatype CommitmentPolicy = 
            FORBID_ENCRYPT_FORBID_DECRYPT |
            REQUIRE_ENCRYPT_ALLOW_DECRYPT |
            REQUIRE_ENCRYPT_REQUIRE_DECRYPT

        datatype AlgorithmSuite = 
            ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY |
            ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
            // TODO: the rest

        datatype PaddingScheme =
            PKCS1 |
            OAEP_SHA1_MGF1 |
            OAEP_SHA256_MGF1 |
            OAEP_SHA384_MGF1 |
            OAEP_SHA512_MGF1
    }

    module Keyrings {
        import Structures
        import opened Wrappers
        import UTF8

        // For the input structures, we could remove these wrapper structures and inline the contained
        // structures (in this case, encryption/decryption materials) directly in method signatures.
        // But we cannot do the same for output, so for now we choose to give everything the wrapper
        // to retain symmetry.
        datatype OnEncryptInput = OnEncryptInput(nameonly materials: Structures.EncryptionMaterials)
        datatype OnEncryptOutput = OnEncryptOutput(nameonly materials: Structures.EncryptionMaterials)
        datatype OnDecryptInput = OnDecryptInput(nameonly materials: Structures.DecryptionMaterials)
        datatype OnDecryptOutput = OnDecryptOutput(nameonly materials: Structures.DecryptionMaterials)

        // TODO: Naming convention for interfaces/traits?
        trait IKeyring {
            method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
            method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
        }
    }

    module CMMs {
        import Structures
        import CryptoConfig
        import opened Wrappers
        import KMS

        datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(
            nameonly encryptionContext: Structures.EncryptionContext,
            nameonly algorithmSuite: Option<CryptoConfig.AlgorithmSuite>,
            nameonly maxPlaintextLength: int
        )

        datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
            nameonly materials: Structures.EncryptionMaterials
        )

        datatype DecryptMaterialsInput = DecryptMaterialsInput(
            nameonly encryptionContext: Structures.EncryptionContext,
            nameonly commitmentPolicy: CryptoConfig.CommitmentPolicy,
            nameonly algorithmSuite: CryptoConfig.AlgorithmSuite,
            nameonly encryptedDataKeys: Structures.EncryptedDataKeyList
        )

        datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
            nameonly decryptionMaterials: Structures.DecryptionMaterials
        )

        trait ICryptographicMaterialProvider {
            method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
            method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
        }
    }

    // Creation inputs
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KMS.KmsKeyId,
        nameonly grantTokens: KMS.GrantTokenList,
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService
    )

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: KMS.KmsKeyId,
        nameonly kmsKeyIds: KMS.KmsKeyIdList,
        nameonly grantTokens: KMS.GrantTokenList,
        nameonly clientSupplier: KMS.IClientSupplier
    )

    // TODO: Naming convention for interfaces/traits?
    // TODO: eventually should return a Result<>, but Dafny currently doesn't support traits as parameters to Result<>
    trait IAwsCryptographicMaterialProvidersClient {
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: Keyrings.IKeyring)
        // TODO: Others
    }

    class AwsCryptographicMaterialProvidersClient extends IAwsCryptographicMaterialProvidersClient {
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: Keyrings.IKeyring) {
            // TODO: Manually implemented. Won't live here, but kept here for illustration for now.
        }
    }
}