// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../KMS/AmazonKeyManagementService.dfy"
include "./KeyManagementService.dfy"

module {:extern "Dafny.Aws.Crypto"} Aws.Crypto {
    import opened Wrappers
    import KMS = Com.Amazonaws.Kms
    import opened UInt = StandardLibrary.UInt
    import opened UTF8

    // TODO this is currently needed for proof stability reasons, otherwise any file that has a transitive dependency on this one tries to
    // load too much at once, making the verification unstable
    export
      provides UTF8, UInt, Wrappers, IKeyring.OnDecrypt,
        ICryptographicMaterialsManager.GetEncryptionMaterials, ICryptographicMaterialsManager.DecryptMaterials, IKeyring.OnEncrypt,
        IAwsCryptographicMaterialsProviderClient.CreateRawAesKeyring, IAwsCryptographicMaterialsProviderClient.CreateDefaultCryptographicMaterialsManager
      reveals AlgorithmSuiteId, EncryptedDataKey, EncryptedDataKeyList, IKeyring, GetEncryptionMaterialsInput, GetEncryptionMaterialsOutput,
        DecryptMaterialsInput, DecryptMaterialsOutput, ICryptographicMaterialsManager, EncryptionContext, EncryptionMaterials, DecryptionMaterials,
        OnEncryptInput, OnEncryptOutput, OnDecryptInput, OnDecryptOutput,
        EncryptionMaterials.Valid, CreateRawAesKeyringInput, CreateDefaultCryptographicMaterialsManagerInput,
        IAwsCryptographicMaterialsProviderClient, AesWrappingAlg

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

    // TODO remove workaround
    trait IKmsClient {}

    trait IClientSupplier {
        // TODO
        // method GetClient(input: GetClientInput) returns (res: AmazonKeyManagementService.IAmazonKeyManagementService)
        method GetClient(input: GetClientInput) returns (res: IKmsClient)
    }

    /////////////
    // structures.smithy
    // TODO: May eventually change this to strings, for now leaving as utf8 bytes for
    // compatibility with existing code.
    type EncryptionContext = map<ValidUTF8Bytes, ValidUTF8Bytes>

    datatype EncryptedDataKey = EncryptedDataKey(nameonly keyProviderId: ValidUTF8Bytes,
                                                 nameonly keyProviderInfo: seq<uint8>,
                                                 nameonly ciphertext: seq<uint8>)

    type EncryptedDataKeyList = seq<EncryptedDataKey>

    datatype EncryptionMaterials = EncryptionMaterials(nameonly algorithmSuiteId: AlgorithmSuiteId, // TODO update to algorithmSuite or update Smithy model (and elsewhere)
                                                       nameonly encryptionContext: EncryptionContext, // TODO should EC be an Option? (and elsewhere)
                                                       nameonly encryptedDataKeys: EncryptedDataKeyList, // TODO should this be an Option? (and elsewhere)
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

    datatype OnEncryptInput = OnEncryptInput(nameonly materials: EncryptionMaterials)

    datatype OnEncryptOutput = OnEncryptOutput(nameonly materials: EncryptionMaterials)
    datatype OnDecryptInput = OnDecryptInput(nameonly materials: DecryptionMaterials,
                                             nameonly encryptedDataKeys: EncryptedDataKeyList)

    datatype OnDecryptOutput = OnDecryptOutput(nameonly materials: DecryptionMaterials)

    trait {:termination false} IKeyring {
        method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
        method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
    }

    /////////////////
    // caching.smithy
    datatype CacheUsageMetadata = CacheUsageMetadata(
        messageUsage: int64,
        byteUsage: int64
    )

    datatype EncryptEntry = EncryptEntry(
        identifier: seq<uint8>,
        encryptionMaterials: EncryptionMaterials,
        creationTime: int64,
        expiryTime: int64,
        usageMetadata: CacheUsageMetadata
    )

    datatype DecryptEntry = DecryptEntry(
        identifier: seq<uint8>,
        decryptionMaterials: DecryptionMaterials,
        creationTime: int64,
        expiryTime: int64,
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
        // TODO
        // nameonly commitmentPolicy: CommitmentPolicy,
        nameonly algorithmSuiteId: Option<AlgorithmSuiteId>,
        nameonly maxPlaintextLength: Option<int64>
    )

    datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
        nameonly encryptionMaterials: EncryptionMaterials
    )

    datatype DecryptMaterialsInput = DecryptMaterialsInput(
        nameonly algorithmSuiteId: AlgorithmSuiteId,
        // TODO
        // nameonly commitmentPolicy: CommitmentPolicy,
        nameonly encryptedDataKeys: EncryptedDataKeyList,
        nameonly encryptionContext: EncryptionContext
    )

    datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
        nameonly decryptionMaterials: DecryptionMaterials
    )

    trait {:termination false} ICryptographicMaterialsManager {
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
        nameonly kmsClient: KMS.IKeyManagementServiceClient
    )

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly clientSupplier: IClientSupplier?
    )

    // KMS - MRK Aware, Discovery
    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
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
        nameonly wrappingKey: seq<uint8>,
        // TODO update spec with wrappingAlg input to Raw AES Keyring init
        nameonly wrappingAlg: AesWrappingAlg
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
        nameonly cacheLimitTtl: int32,
        nameonly keyring: IKeyring?,
        nameonly materialsManager: ICryptographicMaterialsManager?,
        nameonly partitionId: Option<string>,
        nameonly limitBytes: Option<int64>,
        nameonly limitMessages: Option<int64>
    )

    // Caching creation structures
    datatype CreateLocalCryptoMaterialsCacheInput = CreateLocalCryptoMaterialsCacheInput(
        nameonly entryCapacity: int32,
        nameonly entryPruningTailSize: Option<int32>
    )

    // TODO: Return Result<> once supported with traits
    // TODO: Add in Create methods once new Keyrings/CMMs are ready
    trait {:termination false} IAwsCryptographicMaterialsProviderClient {

        // Keyrings
        //method CreateAwsKmsKeyring(input: CreateAwsKmsKeyringInput) returns (res: IKeyring)
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput) returns (res: IKeyring)
        // method CreateMrkAwareStrictMultiKeyring(input: CreateMrkAwareStrictMultiKeyringInput) returns (res: IKeyring)
        // method CreateMrkAwareDiscoveryAwsKmsKeyring(input: CreateMrkAwareDiscoveryAwsKmsKeyringInput) returns (res: IKeyring)
        // method CreateMrkAwareDiscoveryMultiKeyring(input: CreateMrkAwareDiscoveryMultiKeyringInput) returns (res: IKeyring)
        // method CreateMultiKeyring(input: CreateMultiKeyringInput) returns (res: IKeyring)
        method CreateRawAesKeyring(input: CreateRawAesKeyringInput) returns (res: IKeyring)
        // method CreateRawRsaKeyring(input: CreateRawRsaKeyringInput) returns (res: IKeyring)

        // CMMs
        method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)
        // method CreateCachingCryptographicMaterialsManager(input: CreateCachingCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)

        // Caches
        // method CreateLocalCryptoMaterialsCache(input: CreateLocalCryptoMaterialsCacheInput) returns (res: ICryptoMaterialsCache)
    }
}
