include "../../Util/UTF8.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../KMS/AmazonKeyManagementService.dfy"

module {:extern "CryptographicMaterialProviders"} CryptographicMaterialProviders {
    import opened Wrappers
    import AmazonKeyManagementService
    import opened UInt = StandardLibrary.UInt

    // TODO: KMS client will live here
    // TODO: How much value do we get out of the FooList types?
    module KMS {
        import UTF8
        import AmazonKeyManagementService

        type KmsKeyId = string
        type KmsKeyIdList = seq<KmsKeyId>

        type GrantToken = string
        type GrantTokenList = seq<GrantToken>

        type Region = string
        type RegionList = seq<Region>

        datatype DiscoveryFilter = DiscoveryFilter(accountId: string, partition: string)

        datatype GetClientInput = GetClientInput(region: string)

        trait IClientSupplier {
            method GetClient(input: GetClientInput) returns (res: AmazonKeyManagementService.IAmazonKeyManagementService)
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
        // (for example: if the algorithm suite includes signing, the signingKey must not be null).
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
            ALG_AES_128_GCM_IV12_TAG16_NO_KDF |
            ALG_AES_192_GCM_IV12_TAG16_NO_KDF |
            ALG_AES_256_GCM_IV12_TAG16_NO_KDF |
            ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 |
            ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 |
            ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 |
            ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 |
            ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 |
            ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 |
            ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY |
            ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384

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

        trait IKeyring {
            method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
            method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
        }
    }

    module Caching {
        import opened UInt = StandardLibrary.UInt
        import Structures

        datatype CacheUsageMetadata = CacheUsageMetadata(
            messageUsage: int,
            byteUsage: int
        )

        datatype EncryptEntry = EncryptEntry(
            identifier: seq<uint8>,
            encryptionMaterials: Structures.EncryptionMaterials,
            creationTime: int,
            expiryTime: int,
            usageMetadata: CacheUsageMetadata
        )
        datatype DecryptEntry = DecryptEntry(
            identifier: seq<uint8>,
            decryptionMaterials: Structures.DecryptionMaterials,
            creationTime: int,
            expiryTime: int,
            usageMetadata: CacheUsageMetadata
        )

        datatype PutEntryForEncryptInput = PutEntryForEncryptInput(
            identifier: seq<uint8>,
            encryptionMaterials: Structures.EncryptionMaterials,
            usageMetadata: CacheUsageMetadata
        )
        datatype PutEntryForEncryptOutput = PutEntryForEncryptOutput() // empty for now

        datatype GetEntryForEncryptInput = GetEntryForEncryptInput(identifier: seq<uint8>)
        datatype GetEntryForEncryptOutput = GetEntryForEncryptOutput(cacheEntry: EncryptEntry)

        datatype PutEntryForDecryptInput = PutEntryForDecryptInput(
            identifier: seq<uint8>,
            decryptionMaterials: Structures.DecryptionMaterials
        )
        datatype PutEntryForDecryptOutput = PutEntryForDecryptOutput() // empty for now
        
        datatype GetEntryForDecryptInput = GetEntryForDecryptInput(identifier: seq<uint8>)
        datatype GetEntryForDecryptOutput = GetEntryForDecryptOutput(cacheEntry: DecryptEntry)

        datatype DeleteEntryInput = DeleteEntryInput(identifier: seq<uint8>)
        datatype DeleteEntryOutput = DeleteEntryOutput() // empty for now

        trait ICryptoMaterialsCache {
            method PutEntryForEncrypt(input: PutEntryForEncryptInput) returns (res: PutEntryForEncryptOutput)
            method GetEntryForEncrypt(input: GetEntryForEncryptInput) returns (res: GetEntryForEncryptOutput)
            
            method PutEntryForDecrypt(input: PutEntryForDecryptInput) returns (res: PutEntryForDecryptOutput)
            method GetEntryForDecrypt(input: GetEntryForDecryptInput) returns (res: GetEntryForDecryptOutput)

            method DeleteEntry(input: DeleteEntryInput) returns (res: DeleteEntryOutput)
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

        trait ICryptographicMaterialsManager {
            method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
            method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
        }
    }

    // Keyring creation input structures

    // KMS - Old Style
    datatype CreateAwsKmsKeyringInput = CreateAwsKmsKeyringInput(
        nameonly clientSupplier: KMS.IClientSupplier,
        nameonly generator: Option<KMS.KmsKeyId>,
        nameonly keyIds: Option<KMS.KmsKeyIdList>,
        grantTokens: Option<KMS.GrantTokenList>
    )

    // KMS - MRK Aware, Strict
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KMS.KmsKeyId,
        nameonly grantTokens: Option<KMS.GrantTokenList>,
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService
    )

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: Option<KMS.KmsKeyId>,
        nameonly kmsKeyIds: Option<KMS.KmsKeyIdList>,
        nameonly grantTokens: Option<KMS.GrantTokenList>,
        nameonly clientSupplier: KMS.IClientSupplier?
    )

    // KMS - MRK Aware, Discovery
    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService,
        nameonly discoveryFilter: Option<KMS.DiscoveryFilter>,
        nameonly grantTokens: Option<KMS.GrantTokenList>
    )

    datatype CreateMrkAwareDiscoveryMultiKeyringInput = CreateMrkAwareDiscoveryMultiKeyringInput(
        nameonly regions: KMS.RegionList,
        nameonly discoveryFilter: Option<KMS.DiscoveryFilter>,
        nameonly grantTokens: Option<KMS.GrantTokenList>,
        nameonly clientSupplier: KMS.IClientSupplier?
    )

    // Multi
    datatype CreateMultiKeyringInput = CreateMultiKeyringInput(
        nameonly generator: Keyrings.IKeyring?,
        nameonly childKeyrings: Option<seq<Keyrings.IKeyring>>
    )

    // Raw Keyrings
    datatype CreateRawAesKeyringInput = CreateRawAesKeyringInput(
        nameonly keyNamespace: string,
        nameonly keyName: string,
        nameonly wrappingKey: seq<uint8>
    )

    datatype CreateRawRsaKeyringInput = CreateRawRsaKeyringInput(
        nameonly keyNamespace: string,
        nameonly keyName: string,
        nameonly paddingScheme: CryptoConfig.PaddingScheme,
        nameonly publicKey: Option<seq<uint8>>,
        nameonly privateKey: Option<seq<uint8>>
    )

    // CMM Creation input structures

    datatype CreateDefaultCryptographicMaterialsManagerInput = CreateDefaultCryptographicMaterialsManagerInput(
        nameonly keyring: Keyrings.IKeyring
    )

    datatype CreateCachingCryptographicMaterialsManagerInput = CreateCachingCryptographicMaterialsManagerInput(
        nameonly cache: Caching.ICryptoMaterialsCache,
        nameonly cacheLimitTtl: int,
        nameonly keyring: Keyrings.IKeyring?,
        nameonly materialsManager: CMMs.ICryptographicMaterialsManager?,
        nameonly partitionId: Option<string>,
        nameonly limitBytes: Option<int>,
        nameonly limitMessages: Option<int>
    )

    // Caching creation structures
    datatype CreateLocalCryptoMaterialsCacheInput = CreateLocalCryptoMaterialsCacheInput(
        nameonly entryCapacity: int,
        nameonly entryPruningTailSize: Option<int>
    )

    // TODO: Return Result<> once supported with traits
    trait IAwsCryptographicMaterialProvidersClient {

        // Keyrings
        method CreateAwsKmsKeyring(Input: CreateAwsKmsKeyringInput) returns (res: Keyrings.IKeyring) 
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateMrkAwareStrictMultiKeyring(input: CreateMrkAwareStrictMultiKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateMrkAwareDiscoveryAwsKmsKeyring(input: CreateMrkAwareDiscoveryAwsKmsKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateMrkAwareDiscoveryMultiKeyring(input: CreateMrkAwareDiscoveryMultiKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateMultiKeyring(input: CreateMultiKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateRawAesKeyring(input: CreateRawAesKeyringInput) returns (res: Keyrings.IKeyring)
        method CreateRawRsaKeyring(input: CreateRawRsaKeyringInput) returns (res: Keyrings.IKeyring)

        // CMMs
        method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput) returns (res: CMMs.ICryptographicMaterialsManager)
        method CreateCachingCryptographicMaterialsManager(input: CreateCachingCryptographicMaterialsManagerInput) returns (res: CMMs.ICryptographicMaterialsManager)

        // Caches
        method CreateLocalCryptoMaterialsCache(input: CreateLocalCryptoMaterialsCacheInput) returns (res: Caching.ICryptoMaterialsCache)
    }
}