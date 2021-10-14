include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../KMS/AmazonKeyManagementService.dfy"

module {:extern "Dafny.Aws.Crypto"} Aws.Crypto {
    import opened Wrappers
    import AmazonKeyManagementService
    import opened UInt = StandardLibrary.UInt
    import UTF8

    /////////////
    // kms.smithy
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

    /////////////
    // structures.smithy
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
                                                        nameonly algorithm: Option<AlgorithmSuite>,
                                                        nameonly plaintextDataKey: Option<seq<uint8>>,
                                                        nameonly encryptedDataKeys: Option<seq<ValidEncryptedDataKey>>,
                                                        nameonly signingKey: Option<seq<uint8>>)

    datatype DecryptionMaterials = DecryptionMaterials(nameonly encryptionContext: Option<EncryptionContext>,
                                                        nameonly algorithm: Option<AlgorithmSuite>,
                                                        nameonly plaintextDataKey: Option<seq<uint8>>,
                                                        nameonly verificationKey: Option<seq<uint8>>)

    ///////////////////////
    // crypto-config.smithy
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

    //////////////////
    // keyrings.smithy

    // For the input structures, we could remove these wrapper structures and inline the contained
    // structures (in this case, encryption/decryption materials) directly in method signatures.
    // But we cannot do the same for output, so for now we choose to give everything the wrapper
    // to retain symmetry.
    datatype OnEncryptInput = OnEncryptInput(nameonly materials: EncryptionMaterials)
    datatype OnEncryptOutput = OnEncryptOutput(nameonly materials: EncryptionMaterials)
    datatype OnDecryptInput = OnDecryptInput(nameonly materials: DecryptionMaterials)
    datatype OnDecryptOutput = OnDecryptOutput(nameonly materials: DecryptionMaterials)

    trait IKeyring {
        method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
        method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
    }

    /////////////////
    // caching.smithy
    datatype CacheUsageMetadata = CacheUsageMetadata(
        messageUsage: int,
        byteUsage: int
    )

    datatype EncryptEntry = EncryptEntry(
        identifier: seq<uint8>,
        encryptionMaterials: EncryptionMaterials,
        creationTime: int,
        expiryTime: int,
        usageMetadata: CacheUsageMetadata
    )
    datatype DecryptEntry = DecryptEntry(
        identifier: seq<uint8>,
        decryptionMaterials: DecryptionMaterials,
        creationTime: int,
        expiryTime: int,
        usageMetadata: CacheUsageMetadata
    )

    datatype PutEntryForEncryptInput = PutEntryForEncryptInput(
        identifier: seq<uint8>,
        encryptionMaterials: EncryptionMaterials,
        usageMetadata: CacheUsageMetadata
    )
    datatype PutEntryForEncryptOutput = PutEntryForEncryptOutput() // empty for now

    datatype GetEntryForEncryptInput = GetEntryForEncryptInput(identifier: seq<uint8>)
    datatype GetEntryForEncryptOutput = GetEntryForEncryptOutput(cacheEntry: EncryptEntry)

    datatype PutEntryForDecryptInput = PutEntryForDecryptInput(
        identifier: seq<uint8>,
        decryptionMaterials: DecryptionMaterials
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

    //////////////
    // cmms.smithy
    datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(
        nameonly encryptionContext: EncryptionContext,
        nameonly algorithmSuite: Option<AlgorithmSuite>,
        nameonly maxPlaintextLength: int
    )

    datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
        nameonly materials: EncryptionMaterials
    )

    datatype DecryptMaterialsInput = DecryptMaterialsInput(
        nameonly encryptionContext: EncryptionContext,
        nameonly commitmentPolicy: CommitmentPolicy,
        nameonly algorithmSuite: AlgorithmSuite,
        nameonly encryptedDataKeys: EncryptedDataKeyList
    )

    datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
        nameonly decryptionMaterials: DecryptionMaterials
    )

    trait ICryptographicMaterialsManager {
        method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
        method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
    }

    // Keyring creation input structures

    // KMS - Old Style
    datatype CreateAwsKmsKeyringInput = CreateAwsKmsKeyringInput(
        nameonly clientSupplier: IClientSupplier,
        nameonly generator: Option<KmsKeyId>,
        nameonly keyIds: Option<KmsKeyIdList>,
        grantTokens: Option<GrantTokenList>
    )

    // KMS - MRK Aware, Strict
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService
    )

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly clientSupplier: IClientSupplier?
    )

    // KMS - MRK Aware, Discovery
    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>
    )

    datatype CreateMrkAwareDiscoveryMultiKeyringInput = CreateMrkAwareDiscoveryMultiKeyringInput(
        nameonly regions: RegionList,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly clientSupplier: IClientSupplier?
    )

    // Multi
    datatype CreateMultiKeyringInput = CreateMultiKeyringInput(
        nameonly generator: IKeyring?,
        nameonly childKeyrings: Option<seq<IKeyring>>
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
        nameonly paddingScheme: PaddingScheme,
        nameonly publicKey: Option<seq<uint8>>,
        nameonly privateKey: Option<seq<uint8>>
    )

    // CMM Creation input structures

    datatype CreateDefaultCryptographicMaterialsManagerInput = CreateDefaultCryptographicMaterialsManagerInput(
        nameonly keyring: IKeyring
    )

    datatype CreateCachingCryptographicMaterialsManagerInput = CreateCachingCryptographicMaterialsManagerInput(
        nameonly cache: ICryptoMaterialsCache,
        nameonly cacheLimitTtl: int,
        nameonly keyring: IKeyring?,
        nameonly materialsManager: ICryptographicMaterialsManager?,
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
    trait IAwsCryptographicMaterialsProviderClient {

        // Keyrings
        method CreateAwsKmsKeyring(Input: CreateAwsKmsKeyringInput) returns (res: IKeyring) 
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: IKeyring)
        method CreateMrkAwareStrictMultiKeyring(input: CreateMrkAwareStrictMultiKeyringInput) returns (res: IKeyring)
        method CreateMrkAwareDiscoveryAwsKmsKeyring(input: CreateMrkAwareDiscoveryAwsKmsKeyringInput) returns (res: IKeyring)
        method CreateMrkAwareDiscoveryMultiKeyring(input: CreateMrkAwareDiscoveryMultiKeyringInput) returns (res: IKeyring)
        method CreateMultiKeyring(input: CreateMultiKeyringInput) returns (res: IKeyring)
        method CreateRawAesKeyring(input: CreateRawAesKeyringInput) returns (res: IKeyring)
        method CreateRawRsaKeyring(input: CreateRawRsaKeyringInput) returns (res: IKeyring)

        // CMMs
        method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)
        method CreateCachingCryptographicMaterialsManager(input: CreateCachingCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)

        // Caches
        method CreateLocalCryptoMaterialsCache(input: CreateLocalCryptoMaterialsCacheInput) returns (res: ICryptoMaterialsCache)
    }
}
