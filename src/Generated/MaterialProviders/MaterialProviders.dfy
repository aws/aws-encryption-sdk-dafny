include "../../Util/UTF8.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/AmazonKeyManagementService.dfy"

module {:extern "CryptographicMaterialProviders"} CryptographicMaterialProviders {
    import opened Wrappers
    import AmazonKeyManagementService

    // TODO: don't necessarily need sub-structures here. Perhaps Dafny modules are 1:1 with
    // Smithy namespaces, in which case all of this lives under the "aws.crypto" module.
    // But for now it seems like a nice way of separating things out. Alternatively we could
    // update the Smithy model to have more sub-namespaces ("aws.crypto.structures").
    module Structures {
        import UTF8
        import opened UInt = StandardLibrary.UInt
        import opened Wrappers

        // TODO This lives in the 'keyrings' file in the Smithy model, but I think 'structures'
        // actually makes more sense (or even 'kms'?)
        type EncryptionContext = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>
        type GrantToken = string
        type GrantTokenList = seq<GrantToken>

        datatype EncryptedDataKey = EncryptedDataKey(providerID: UTF8.ValidUTF8Bytes,
                                                    providerInfo: seq<uint8>,
                                                    ciphertext: seq<uint8>)
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

        // Discussion: there are various constraints we could add in a predicate to validate
        // correctness of materials (such as if the algorithm suite includes signing, a signingKey
        // is present). However, we haven't so far been able to model these sorts of constraints
        // in Smithy, so it's not clear that the Smithy-generated code will be able to have them.
        // Perhaps manually implemented?
        datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: Option<EncryptionContext>,
                                                           algorithm: Option<string>,
                                                           plaintextDataKey: Option<seq<uint8>>,
                                                           encryptedDataKeys: Option<seq<ValidEncryptedDataKey>>,
                                                           signingKey: Option<seq<uint8>>)

        datatype DecryptionMaterials = DecryptionMaterials(encryptionContext: Option<EncryptionContext>,
                                                           algorithm: Option<string>,
                                                           plaintextDataKey: Option<seq<uint8>>,
                                                           verificationKey: Option<seq<uint8>>)
    }

    module CryptoConfig {
        // Discusion: we can model commitment policy as an enum like this, with no values.
        // But other enum types (like AlgSuite) do have values we want to associate with them.
        // Since this will eventually be code-genned, we need to be consistent since they're both
        // Smithy enums. Plus the Smithy docs suggest that code generators may choose to represent
        // enums as constants, for better forwards compatibility.
        datatype CommitmentPolicy = FORBID_ENCRYPT_FORBID_DECRYPT | REQUIRE_ENCRYPT_ALLOW_DECRYPT | REQUIRE_ENCRYPT_REQUIRE_DECRYPT

        class AlgorithmSuite {
            const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY               := 0x0478
            const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384    := 0x0578
            // TODO: the rest
        }

        // Padding scheme

    }

    module Keyrings {
        import Structures
        import opened Wrappers
        import UTF8

        // We can consider removing wrapper objects like this and passing the parameters
        // directly as named parameters. 
        datatype OnEncryptInput = OnEncryptInput(materials: Structures.EncryptionMaterials)
        datatype OnEncryptOutput = OnEncryptOutput(materials: Structures.EncryptionMaterials)
        datatype OnDecryptInput = OnDecryptInput(materials: Structures.DecryptionMaterials)
        datatype OnDecryptOutput = OnDecryptOutput(materials: Structures.DecryptionMaterials)

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

        datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(
            encryptionContext: Structures.EncryptionContext,
            algorithmSuite: Option<string>,
            maxPlaintextLength: int
        )

        datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
            materials: Structures.EncryptionMaterials
        )

        datatype DecryptMaterialsInput = DecryptMaterialsInput(
            encryptionContext: Structures.EncryptionContext,
            commitmentPolicy: CryptoConfig.CommitmentPolicy,
            algorithmSuite: string,
            encryptedDataKeys: Structures.EncryptedDataKeyList
        )

        datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
            decryptionMaterials: Structures.DecryptionMaterials
        )

        trait ICryptographicMaterialProvider {
            method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
            method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
        }
    }

    // Creation inputs
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyring(
            kmsKeyId: string,
            grantTokens: Structures.GrantTokenList,
            kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService
    )

    // TODO: Naming convention for interfaces/traits?
    // TODO: removed Result<> return because it does not accept traits
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