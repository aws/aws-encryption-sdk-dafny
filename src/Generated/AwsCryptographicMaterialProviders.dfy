include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../KMS/AmazonKeyManagementService.dfy"

module {:extern "Dafny.Aws.Crypto"} Aws.Crypto {
    import opened Wrappers
    import AmazonKeyManagementService
    import opened UInt = StandardLibrary.UInt
    import UTF8

    // TODO this is currently needed for proof stability reasons, otherwise any file that has a transitive dependency on this one tries to
    // load too much at once, making the verification unstable
    export
      provides UTF8, UInt, Wrappers, IKeyring.OnDecrypt,
        ICryptographicMaterialsManager.GetEncryptionMaterials, ICryptographicMaterialsManager.DecryptMaterials, IKeyring.OnEncrypt,
        IAwsCryptographicMaterialsProviderClient.CreateRawAesKeyring, IAwsCryptographicMaterialsProviderClient.CreateDefaultCryptographicMaterialsManager
      reveals AlgorithmSuiteId, EncryptedDataKey, EncryptedDataKey.Valid, IKeyring, GetEncryptionMaterialsInput, GetEncryptionMaterialsOutput,
        DecryptMaterialsInput, DecryptMaterialsOutput, ICryptographicMaterialsManager, EncryptionContext, EncryptionMaterials, DecryptionMaterials,
        ValidEncryptedDataKey, EncryptedDataKeyList, OnEncryptInput, OnEncryptOutput, OnDecryptInput, OnDecryptOutput, OnEncryptInput.Valid, OnDecryptInput.Valid,
        GetEncryptionMaterialsInput.Valid, DecryptMaterialsInput.Valid, EncryptionMaterials.Valid, CreateRawAesKeyringInput, CreateDefaultCryptographicMaterialsManagerInput,
        IAwsCryptographicMaterialsProviderClient, AesWrappingAlg, CreateDefaultCryptographicMaterialsManagerInput.Valid, CreateRawAesKeyringInput.Valid

    /////////////
    // kms.smithy
    type KmsKeyId = string
    type KmsKeyIdList = seq<KmsKeyId>

    type GrantToken = string
    type GrantTokenList = seq<GrantToken>

    type Region = string
    type RegionList = seq<Region>

    datatype DiscoveryFilter = DiscoveryFilter(accountId: string, partition: string)
    {
        predicate Valid() {
            true
        }
    }

    datatype GetClientInput = GetClientInput(region: string)
    {
        predicate Valid() {
            true
        }
    }

    // TODO remove workaround
    trait IKmsClient {}

    trait IClientSupplier {
        // TODO
        // method GetClient(input: GetClientInput) returns (res: AmazonKeyManagementService.IAmazonKeyManagementService)
        //    requires input.Valid()
        method GetClient(input: GetClientInput) returns (res: IKmsClient)
            requires input.Valid()
    }

    /////////////
    // structures.smithy
    // TODO: May eventually change this to strings, for now leaving as utf8 bytes for
    // compatibility with existing code.
    type EncryptionContext = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

    datatype EncryptedDataKey = EncryptedDataKey(nameonly keyProviderId: UTF8.ValidUTF8Bytes,
                                                 nameonly keyProviderInfo: seq<uint8>,
                                                 nameonly ciphertext: seq<uint8>)
    {
        // TODO: constraints not currently modeled in Smithy
        predicate Valid() {
            |keyProviderId| < UINT16_LIMIT &&
            |keyProviderInfo| < UINT16_LIMIT &&
            |ciphertext| < UINT16_LIMIT
        }
    }
    type ValidEncryptedDataKey = i : EncryptedDataKey | i.Valid() witness *

    type EncryptedDataKeyList = seq<EncryptedDataKey>

    // There are a number of assertions we can make about materials to validate correctness
    // (for example: if the algorithm suite includes signing, the signingKey must not be null).
    // However, we cannot model these in Smithy, so we will need to write them manually in the
    // Dafny code rather than in this auto-generated portion.
    datatype EncryptionMaterials = EncryptionMaterials(nameonly algorithmSuiteId: AlgorithmSuiteId, // TODO update to algorithmSuite or update Smithy model (and elsewhere)
                                                       nameonly encryptionContext: EncryptionContext, // TODO should EC be an Option? (and elsewhere)
                                                       nameonly encryptedDataKeys: seq<ValidEncryptedDataKey>, // TODO should this be an Option? (and elsewhere)
                                                       nameonly plaintextDataKey: Option<seq<uint8>>,
                                                       nameonly signingKey: Option<seq<uint8>>)
    {
        predicate Valid() {
            true
        }
    }

    datatype DecryptionMaterials = DecryptionMaterials(nameonly algorithmSuiteId: AlgorithmSuiteId,
                                                       nameonly encryptionContext: EncryptionContext,
                                                       nameonly plaintextDataKey: Option<seq<uint8>>,
                                                       nameonly verificationKey: Option<seq<uint8>>)
    {
        predicate Valid() {
            true
        }
    }

    ///////////////////////
    // crypto-config.smithy
    datatype CommitmentPolicy =
        FORBID_ENCRYPT_FORBID_DECRYPT |
        REQUIRE_ENCRYPT_ALLOW_DECRYPT |
        REQUIRE_ENCRYPT_REQUIRE_DECRYPT

    datatype AesWrappingAlg =
      ALG_AES128_GCM_IV12_TAG16 |
      ALG_AES192_GCM_IV12_TAG16 |
      ALG_AES256_GCM_IV12_TAG16

    datatype AlgorithmSuiteId =
        ALG_AES_128_GCM_IV12_TAG16_NO_KDF |
        ALG_AES_192_GCM_IV12_TAG16_NO_KDF |
        ALG_AES_256_GCM_IV12_TAG16_NO_KDF |
        ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 |
        ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 |
        ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 |
        ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 |
        ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 |
        ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
        // TODO add commitment suites back in
        // ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY |
        // ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384

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
    {
        predicate Valid() {
            true
        }
    }

    datatype OnEncryptOutput = OnEncryptOutput(nameonly materials: EncryptionMaterials)
    {
        predicate Valid() {
            true
        }
    }
    datatype OnDecryptInput = OnDecryptInput(nameonly materials: DecryptionMaterials,
                                             nameonly encryptedDataKeys: EncryptedDataKeyList)
    {
        predicate Valid() {
            true
        }
    }

    datatype OnDecryptOutput = OnDecryptOutput(nameonly materials: DecryptionMaterials)
    {
        predicate Valid() {
            true
        }
    }

    trait {:termination false} IKeyring {
        method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
            requires input.Valid()
        method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
            requires input.Valid()
    }

    /////////////////
    // caching.smithy
    datatype CacheUsageMetadata = CacheUsageMetadata(
        messageUsage: int64,
        byteUsage: int64
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype EncryptEntry = EncryptEntry(
        identifier: seq<uint8>,
        encryptionMaterials: EncryptionMaterials,
        creationTime: int64,
        expiryTime: int64,
        usageMetadata: CacheUsageMetadata
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype DecryptEntry = DecryptEntry(
        identifier: seq<uint8>,
        decryptionMaterials: DecryptionMaterials,
        creationTime: int64,
        expiryTime: int64,
        usageMetadata: CacheUsageMetadata
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype PutEntryForEncryptInput = PutEntryForEncryptInput(
        identifier: seq<uint8>,
        encryptionMaterials: EncryptionMaterials,
        usageMetadata: CacheUsageMetadata
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype PutEntryForEncryptOutput = PutEntryForEncryptOutput() // empty for now
    {
        predicate Valid() {
            true
        }
    }

    datatype GetEntryForEncryptInput = GetEntryForEncryptInput(identifier: seq<uint8>)
    {
        predicate Valid() {
            true
        }
    }

    datatype GetEntryForEncryptOutput = GetEntryForEncryptOutput(cacheEntry: EncryptEntry)
    {
        predicate Valid() {
            true
        }
    }

    datatype PutEntryForDecryptInput = PutEntryForDecryptInput(
        identifier: seq<uint8>,
        decryptionMaterials: DecryptionMaterials
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype PutEntryForDecryptOutput = PutEntryForDecryptOutput() // empty for now
    {
        predicate Valid() {
            true
        }
    }

    datatype GetEntryForDecryptInput = GetEntryForDecryptInput(identifier: seq<uint8>)
    {
        predicate Valid() {
            true
        }
    }

    datatype GetEntryForDecryptOutput = GetEntryForDecryptOutput(cacheEntry: DecryptEntry)
    {
        predicate Valid() {
            true
        }
    }

    datatype DeleteEntryInput = DeleteEntryInput(identifier: seq<uint8>)
    {
        predicate Valid() {
            true
        }
    }

    datatype DeleteEntryOutput = DeleteEntryOutput() // empty for now
    {
        predicate Valid() {
            true
        }
    }

    trait ICryptoMaterialsCache {
        method PutEntryForEncrypt(input: PutEntryForEncryptInput) returns (res: PutEntryForEncryptOutput)
            requires input.Valid()
        method GetEntryForEncrypt(input: GetEntryForEncryptInput) returns (res: GetEntryForEncryptOutput)
            requires input.Valid()

        method PutEntryForDecrypt(input: PutEntryForDecryptInput) returns (res: PutEntryForDecryptOutput)
            requires input.Valid()
        method GetEntryForDecrypt(input: GetEntryForDecryptInput) returns (res: GetEntryForDecryptOutput)
            requires input.Valid()

        method DeleteEntry(input: DeleteEntryInput) returns (res: DeleteEntryOutput)
            requires input.Valid()
    }

    //////////////
    // cmms.smithy
    datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(
        nameonly encryptionContext: EncryptionContext,
        // TODO
        // nameonly commitmentPolicy: CommitmentPolicy,
        nameonly algorithmSuiteId: Option<AlgorithmSuiteId>,
        nameonly maxPlaintextLength: Option<int64>
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
        nameonly encryptionMaterials: EncryptionMaterials
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype DecryptMaterialsInput = DecryptMaterialsInput(
        nameonly algorithmSuiteId: AlgorithmSuiteId,
        // TODO
        // nameonly commitmentPolicy: CommitmentPolicy,
        nameonly encryptedDataKeys: EncryptedDataKeyList,
        nameonly encryptionContext: EncryptionContext
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
        nameonly decryptionMaterials: DecryptionMaterials
    )
    {
        predicate Valid() {
            true
        }
    }

    trait {:termination false} ICryptographicMaterialsManager {
        method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
            requires input.Valid()
        method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
            requires input.Valid()
    }

    // Keyring creation input structures

    // KMS - Old Style
    datatype CreateAwsKmsKeyringInput = CreateAwsKmsKeyringInput(
        nameonly clientSupplier: IClientSupplier,
        nameonly generator: Option<KmsKeyId>,
        nameonly keyIds: Option<KmsKeyIdList>,
        grantTokens: Option<GrantTokenList>
    )
    {
        predicate Valid() {
            true
        }
    }

    // KMS - MRK Aware, Strict
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly clientSupplier: IClientSupplier?
    )
    {
        predicate Valid() {
            true
        }
    }

    // KMS - MRK Aware, Discovery
    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(
        nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype CreateMrkAwareDiscoveryMultiKeyringInput = CreateMrkAwareDiscoveryMultiKeyringInput(
        nameonly regions: RegionList,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly clientSupplier: IClientSupplier?
    )
    {
        predicate Valid() {
            true
        }
    }

    // Multi
    datatype CreateMultiKeyringInput = CreateMultiKeyringInput(
        nameonly generator: IKeyring?,
        nameonly childKeyrings: Option<seq<IKeyring>>
    )
    {
        predicate Valid() {
            true
        }
    }

    // Raw Keyrings
    datatype CreateRawAesKeyringInput = CreateRawAesKeyringInput(
        nameonly keyNamespace: string,
        nameonly keyName: string,
        nameonly wrappingKey: seq<uint8>,
        // TODO update spec with wrappingAlg input to Raw AES Keyring init
        nameonly wrappingAlg: AesWrappingAlg
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype CreateRawRsaKeyringInput = CreateRawRsaKeyringInput(
        nameonly keyNamespace: string,
        nameonly keyName: string,
        nameonly paddingScheme: PaddingScheme,
        nameonly publicKey: Option<seq<uint8>>,
        nameonly privateKey: Option<seq<uint8>>
    )
    {
        predicate Valid() {
            true
        }
    }

    // CMM Creation input structures

    datatype CreateDefaultCryptographicMaterialsManagerInput = CreateDefaultCryptographicMaterialsManagerInput(
        nameonly keyring: IKeyring
    )
    {
        predicate Valid() {
            true
        }
    }

    datatype CreateCachingCryptographicMaterialsManagerInput = CreateCachingCryptographicMaterialsManagerInput(
        nameonly cache: ICryptoMaterialsCache,
        nameonly cacheLimitTtl: int32,
        nameonly keyring: IKeyring?,
        nameonly materialsManager: ICryptographicMaterialsManager?,
        nameonly partitionId: Option<string>,
        nameonly limitBytes: Option<int64>,
        nameonly limitMessages: Option<int64>
    )
    {
        predicate Valid() {
            true
        }
    }

    // Caching creation structures
    datatype CreateLocalCryptoMaterialsCacheInput = CreateLocalCryptoMaterialsCacheInput(
        nameonly entryCapacity: int32,
        nameonly entryPruningTailSize: Option<int32>
    )
    {
        predicate Valid() {
            true
        }
    }

    // TODO: Return Result<> once supported with traits
    // TODO: Add in Create methods once new Keyrings/CMMs are ready
    trait {:termination false} IAwsCryptographicMaterialsProviderClient {

        // Keyrings
        //method CreateAwsKmsKeyring(input: CreateAwsKmsKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        // method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        // method CreateMrkAwareStrictMultiKeyring(input: CreateMrkAwareStrictMultiKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        // method CreateMrkAwareDiscoveryAwsKmsKeyring(input: CreateMrkAwareDiscoveryAwsKmsKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        // method CreateMrkAwareDiscoveryMultiKeyring(input: CreateMrkAwareDiscoveryMultiKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        // method CreateMultiKeyring(input: CreateMultiKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()
        method CreateRawAesKeyring(input: CreateRawAesKeyringInput) returns (res: IKeyring)
            requires input.Valid()
        // method CreateRawRsaKeyring(input: CreateRawRsaKeyringInput) returns (res: IKeyring)
        //     requires input.Valid()

        // CMMs
        method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)
            requires input.Valid()
        // method CreateCachingCryptographicMaterialsManager(input: CreateCachingCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)
        //    requires input.Valid()

        // Caches
        // method CreateLocalCryptoMaterialsCache(input: CreateLocalCryptoMaterialsCacheInput) returns (res: ICryptoMaterialsCache)
        //    requires input.Valid()
    }
}
