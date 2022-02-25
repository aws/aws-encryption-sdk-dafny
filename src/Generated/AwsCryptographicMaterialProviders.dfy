// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Util/UTF8.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/KeyManagementService.dfy"
include "./KeyManagementService.dfy"

module {:extern "Dafny.Aws.Crypto"} Aws.Crypto {
    import opened Wrappers
    import KMS = Com.Amazonaws.Kms
    import opened UInt = StandardLibrary.UInt
    import opened UTF8

    // TODO this is currently needed for proof stability reasons, otherwise any file that has a transitive dependency on this one tries to
    // load too much at once, making the verification unstable
    export
      provides UTF8, UInt, KMS, Wrappers,
        IClientSupplier,
        IClientSupplier.GetClient,
        IKeyring.OnDecrypt,
        IKeyring.OnEncrypt,
        ICryptographicMaterialsManager.GetEncryptionMaterials,
        ICryptographicMaterialsManager.DecryptMaterials,
        IAwsCryptographicMaterialsProviderClient.CreateRawAesKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateDefaultCryptographicMaterialsManager,
        IAwsCryptographicMaterialsProviderClient.CreateStrictAwsKmsKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateAwsKmsDiscoveryKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateMrkAwareStrictAwsKmsKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateMrkAwareDiscoveryAwsKmsKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateMultiKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateRawRsaKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateDefaultClientSupplier,
        IAwsCryptographicMaterialsProviderClient.CreateMrkAwareStrictMultiKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateMrkAwareDiscoveryMultiKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateStrictAwsKmsMultiKeyring,
        IAwsCryptographicMaterialsProviderClient.CreateAwsKmsDiscoveryMultiKeyring,
        AwsCryptographicMaterialProvidersClientException.message,
        AwsCryptographicMaterialProvidersClientException.WrapResultString,
        AwsCryptographicMaterialProvidersClientException.WrapOutcomeString,
        Need

      reveals
        AlgorithmSuiteId,
        EncryptedDataKey,
        EncryptedDataKeyList,
        IKeyring,
        GetEncryptionMaterialsInput,
        GetEncryptionMaterialsOutput,
        DecryptMaterialsInput,
        DecryptMaterialsOutput,
        ICryptographicMaterialsManager,
        EncryptionContext,
        EncryptionMaterials,
        DecryptionMaterials,
        OnEncryptInput,
        OnEncryptOutput,
        OnDecryptInput,
        OnDecryptOutput,
        EncryptionMaterials.Valid,
        CreateStrictAwsKmsKeyringInput,
        CreateAwsKmsDiscoveryKeyringInput,
        CreateDefaultClientSupplierInput,
        CreateDefaultCryptographicMaterialsManagerInput,
        CreateMrkAwareDiscoveryAwsKmsKeyringInput,
        CreateMrkAwareStrictAwsKmsKeyringInput,
        CreateMultiKeyringInput,
        CreateRawAesKeyringInput,
        CreateMrkAwareStrictMultiKeyringInput,
        CreateMrkAwareDiscoveryMultiKeyringInput,
        CreateStrictAwsKmsMultiKeyringInput,
        CreateAwsKmsDiscoveryMultiKeyringInput,
        DiscoveryFilter,
        AccountId,
        AccountIdList,
        KmsKeyId,
        GrantToken,
        GrantTokenList,
        IAwsCryptographicMaterialsProviderClient,
        IClientSupplier,
        GetClientInput,
        IAwsCryptographicMaterialProvidersException,
        IAwsCryptographicMaterialProvidersException.GetMessage,
        AwsCryptographicMaterialProvidersClientException,
        AwsCryptographicMaterialProvidersClientException.GetMessage,
        AesWrappingAlg,
        CommitmentPolicy,
        CreateRawRsaKeyringInput,
        PaddingScheme,
        KmsKeyIdList,
        RegionList,
        Region

    /////////////
    // kms.smithy
    type KmsKeyId = string
    type KmsKeyIdList = seq<KmsKeyId>

    type GrantToken = string
    type GrantTokenList = seq<GrantToken>

    type Region = string
    type RegionList = seq<Region>

    type AccountId = string
    type AccountIdList = seq<AccountId>

    datatype DiscoveryFilter = DiscoveryFilter(accountIds: AccountIdList, partition: string)

    datatype GetClientInput = GetClientInput(region: string)

    trait {:termination false} IClientSupplier {
        method GetClient(input: GetClientInput)
            returns (res: Result<KMS.IKeyManagementServiceClient, IAwsCryptographicMaterialProvidersException>)
    }

    datatype CreateDefaultClientSupplierInput = CreateDefaultClientSupplierInput()

    /////////////
    // structures.smithy
    // TODO: May eventually change this to strings, for now leaving as utf8 bytes for
    // compatibility with existing code.
    type EncryptionContext = map<ValidUTF8Bytes, ValidUTF8Bytes>

    datatype EncryptedDataKey = EncryptedDataKey(nameonly keyProviderId: ValidUTF8Bytes,
                                                 nameonly keyProviderInfo: seq<uint8>,
                                                 nameonly ciphertext: seq<uint8>)

    type EncryptedDataKeyList = seq<EncryptedDataKey>

    //= compliance/framework/structures.txt#2.3.3.2
    //= type=implication
    //# This structure MAY include
    //# any of the following fields:
    //
    //= compliance/framework/structures.txt#2.3.3.2.4
    //= type=implication
    //# The plaintext data key SHOULD be stored as immutable data.
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

    //= compliance/framework/structures.txt#2.3.4.2
    //= type=implication
    //# This structure MAY include
    //# any of the following fields:
    //
    //= compliance/framework/structures.txt#2.3.4.2.3
    //= type=implication
    //# The plaintext data key SHOULD be stored as immutable data.
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
        FORBID_ENCRYPT_ALLOW_DECRYPT |
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
        method OnEncrypt(input: OnEncryptInput)
            returns (res: Result<OnEncryptOutput, IAwsCryptographicMaterialProvidersException>)
        method OnDecrypt(input: OnDecryptInput)
            returns (res: Result<OnDecryptOutput, IAwsCryptographicMaterialProvidersException>)
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
        method PutEntryForEncrypt(input: PutEntryForEncryptInput)
            returns (res: Result<PutEntryForEncryptOutput, IAwsCryptographicMaterialProvidersException>)
        method GetEntryForEncrypt(input: GetEntryForEncryptInput)
            returns (res: Result<GetEntryForEncryptOutput, IAwsCryptographicMaterialProvidersException>)

        method PutEntryForDecrypt(input: PutEntryForDecryptInput)
            returns (res: Result<PutEntryForDecryptOutput, IAwsCryptographicMaterialProvidersException>)
        method GetEntryForDecrypt(input: GetEntryForDecryptInput)
            returns (res: Result<GetEntryForDecryptOutput, IAwsCryptographicMaterialProvidersException>)

        method DeleteEntry(input: DeleteEntryInput)
            returns (res: Result<DeleteEntryOutput, IAwsCryptographicMaterialProvidersException>)
    }

    //////////////
    // cmms.smithy
    datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(
        nameonly encryptionContext: EncryptionContext,
        nameonly commitmentPolicy: CommitmentPolicy,
        nameonly algorithmSuiteId: Option<AlgorithmSuiteId>,
        nameonly maxPlaintextLength: Option<int64>
    )

    datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(
        nameonly encryptionMaterials: EncryptionMaterials
    )

    datatype DecryptMaterialsInput = DecryptMaterialsInput(
        nameonly algorithmSuiteId: AlgorithmSuiteId,
        nameonly commitmentPolicy: CommitmentPolicy,
        nameonly encryptedDataKeys: EncryptedDataKeyList,
        nameonly encryptionContext: EncryptionContext
    )

    datatype DecryptMaterialsOutput = DecryptMaterialsOutput(
        nameonly decryptionMaterials: DecryptionMaterials
    )

    trait {:termination false} ICryptographicMaterialsManager {
        method GetEncryptionMaterials(input: GetEncryptionMaterialsInput)
            returns (res: Result<GetEncryptionMaterialsOutput, IAwsCryptographicMaterialProvidersException>)
        method DecryptMaterials(input: DecryptMaterialsInput)
            returns (res: Result<DecryptMaterialsOutput, IAwsCryptographicMaterialProvidersException>)
    }

    // Keyring creation input structures

    // KMS
    datatype CreateStrictAwsKmsKeyringInput = CreateStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly grantTokens: Option<GrantTokenList>
	)

    datatype CreateStrictAwsKmsMultiKeyringInput = CreateStrictAwsKmsMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly clientSupplier: Option<IClientSupplier>,
        nameonly grantTokens: Option<GrantTokenList>
    )

    // KMS - Discovery
    datatype CreateAwsKmsDiscoveryKeyringInput = CreateAwsKmsDiscoveryKeyringInput(
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        grantTokens: Option<GrantTokenList>
    )

    datatype CreateAwsKmsDiscoveryMultiKeyringInput = CreateAwsKmsDiscoveryMultiKeyringInput(
        nameonly regions: RegionList,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly clientSupplier: Option<IClientSupplier>,
        nameonly grantTokens: Option<GrantTokenList>
    )


    // KMS - MRK Aware, Strict
    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly grantTokens: Option<GrantTokenList>
    )

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly clientSupplier: Option<IClientSupplier>,
        nameonly grantTokens: Option<GrantTokenList>
    )

    // KMS - MRK Aware, Discovery
    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly region: string
    )

    datatype CreateMrkAwareDiscoveryMultiKeyringInput = CreateMrkAwareDiscoveryMultiKeyringInput(
        nameonly regions: RegionList,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly clientSupplier: Option<IClientSupplier>,
        nameonly grantTokens: Option<GrantTokenList>
    )

    // Multi
    datatype CreateMultiKeyringInput = CreateMultiKeyringInput(
        nameonly generator: Option<IKeyring>,
        nameonly childKeyrings: seq<IKeyring>
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
        nameonly keyring: Option<IKeyring>,
        nameonly materialsManager: Option<ICryptographicMaterialsManager>,
        nameonly partitionId: Option<string>,
        nameonly limitBytes: Option<int64>,
        nameonly limitMessages: Option<int64>
    )

    // Caching creation structures
    datatype CreateLocalCryptoMaterialsCacheInput = CreateLocalCryptoMaterialsCacheInput(
        nameonly entryCapacity: int32,
        nameonly entryPruningTailSize: Option<int32>
    )

    // TODO: Add in Create methods once new Keyrings/CMMs are ready
    trait {:termination false} IAwsCryptographicMaterialsProviderClient {

        // Keyrings
        method CreateStrictAwsKmsKeyring(input: CreateStrictAwsKmsKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateStrictAwsKmsMultiKeyring(input: CreateStrictAwsKmsMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsDiscoveryKeyring(input: CreateAwsKmsDiscoveryKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsDiscoveryMultiKeyring(input: CreateAwsKmsDiscoveryMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateMrkAwareStrictAwsKmsKeyring(input: CreateMrkAwareStrictAwsKmsKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateMrkAwareStrictMultiKeyring(input: CreateMrkAwareStrictMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateMrkAwareDiscoveryAwsKmsKeyring(input: CreateMrkAwareDiscoveryAwsKmsKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateMrkAwareDiscoveryMultiKeyring(input: CreateMrkAwareDiscoveryMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateMultiKeyring(input: CreateMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateRawAesKeyring(input: CreateRawAesKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateRawRsaKeyring(input: CreateRawRsaKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)

        // CMMs
        method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput)
            returns (res: Result<ICryptographicMaterialsManager, IAwsCryptographicMaterialProvidersException>)
        // method CreateCachingCryptographicMaterialsManager(input: CreateCachingCryptographicMaterialsManagerInput)
        //     returns (res: Result<ICryptographicMaterialsManager, IAwsCryptographicMaterialProvidersException>)

        // Client Supplier
        method CreateDefaultClientSupplier(input: CreateDefaultClientSupplierInput)
          returns (res: Result<IClientSupplier, IAwsCryptographicMaterialProvidersException>)

        // Caches
        // method CreateLocalCryptoMaterialsCache(input: CreateLocalCryptoMaterialsCacheInput)
        //     returns (res: Result<ICryptoMaterialsCache, IAwsCryptographicMaterialProvidersException>)
    }

    trait IAwsCryptographicMaterialProvidersException {
        function method GetMessage(): (message: string)
            reads this
    }

    class AwsCryptographicMaterialProvidersClientException extends IAwsCryptographicMaterialProvidersException {
        var message: string

        constructor (message: string) {
            this.message := message;
        }

        function method GetMessage(): (message: string)
            reads this
        {
            this.message
        }

        static method WrapResultString<T>(result: Result<T, string>)
            returns (wrapped: Result<T, IAwsCryptographicMaterialProvidersException>)
            ensures result.Success? ==>
                && wrapped.Success?
                && wrapped.value == result.value
            ensures result.Failure? ==>
                && wrapped.Failure?
        {
            match result {
                case Success(value) => return Result.Success(value);
                case Failure(error) =>
                    var wrappedError := new AwsCryptographicMaterialProvidersClientException(error);
                    return Result.Failure(wrappedError);
            }
        }

        static method WrapOutcomeString(outcome: Outcome<string>)
          returns (wrapped: Outcome<IAwsCryptographicMaterialProvidersException>)
          ensures outcome.Fail? ==> && wrapped.Fail?
        {
          match outcome {
            case Pass => return Pass;
            case Fail(error) =>
              var wrappedError := new AwsCryptographicMaterialProvidersClientException(error);
              return Outcome.Fail(wrappedError);
          }
        }
    }

    // A helper method to ensure a requirement is true at runtime.
    // If the requirement is false, the returned result contains a generic exception that wraps the provided message.
    // :- Need(5 == |mySet|, "The set MUST have 5 elements.")
    //
    // This is like `Wrappers.Need<E>`, except:
    //
    //   - `E` is specialized to be IAwsCryptographicMaterialProvidersException,
    //     and the error string is wrapped in a class implementing that trait
    //   - it's a `method` and not a `function method`, because we must instantiate a `new`
    //     error object and that is not permitted in ghost contexts
    method Need(condition: bool, error: string)
        returns (result: Outcome<IAwsCryptographicMaterialProvidersException>)
        ensures condition <==> result.Pass?
    {
        if condition {
            return Pass;
        } else {
            var exception := new AwsCryptographicMaterialProvidersClientException(error);
            return Fail(exception);
        }
    }
}
