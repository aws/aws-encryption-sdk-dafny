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
        IAwsCryptographicMaterialProviders.CreateRawAesKeyring,
        IAwsCryptographicMaterialProviders.CreateDefaultCryptographicMaterialsManager,
        IAwsCryptographicMaterialProviders.CreateAwsKmsKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsDiscoveryKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsMrkKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsMrkDiscoveryKeyring,
        IAwsCryptographicMaterialProviders.CreateMultiKeyring,
        IAwsCryptographicMaterialProviders.CreateRawRsaKeyring,
        IAwsCryptographicMaterialProviders.CreateDefaultClientSupplier,
        IAwsCryptographicMaterialProviders.CreateAwsKmsMrkMultiKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsMultiKeyring,
        IAwsCryptographicMaterialProviders.CreateAwsKmsDiscoveryMultiKeyring,
        AwsCryptographicMaterialProvidersException.message,
        AwsCryptographicMaterialProvidersException.WrapResultString,
        AwsCryptographicMaterialProvidersException.WrapOutcomeString,
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
        CreateAwsKmsKeyringInput,
        CreateAwsKmsDiscoveryKeyringInput,
        CreateDefaultClientSupplierInput,
        CreateDefaultCryptographicMaterialsManagerInput,
        CreateAwsKmsMrkDiscoveryKeyringInput,
        CreateAwsKmsMrkKeyringInput,
        CreateMultiKeyringInput,
        CreateRawAesKeyringInput,
        CreateAwsKmsMrkMultiKeyringInput,
        CreateAwsKmsMrkDiscoveryMultiKeyringInput,
        CreateAwsKmsMultiKeyringInput,
        CreateAwsKmsDiscoveryMultiKeyringInput,
        DiscoveryFilter,
        AccountId,
        AccountIdList,
        KmsKeyId,
        GrantToken,
        GrantTokenList,
        IAwsCryptographicMaterialProviders,
        IAwsCryptographicMaterialProvidersFactory,
        IClientSupplier,
        GetClientInput,
        IAwsCryptographicMaterialProvidersException,
        IAwsCryptographicMaterialProvidersException.GetMessage,
        AwsCryptographicMaterialProvidersException,
        AwsCryptographicMaterialProvidersException.GetMessage,
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
    //= compliance/client-apis/client.txt#2.4.1
    //= type=implication
    //# The AWS Encryption SDK MUST provide the following commitment
    //# policies:
    //#*  FORBID_ENCRYPT_ALLOW_DECRYPT
    //#*  REQUIRE_ENCRYPT_ALLOW_DECRYPT
    //#*  REQUIRE_ENCRYPT_REQUIRE_DECRYPT
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
    datatype CreateAwsKmsKeyringInput = CreateAwsKmsKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly grantTokens: Option<GrantTokenList>
	)

    datatype CreateAwsKmsMultiKeyringInput = CreateAwsKmsMultiKeyringInput(
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
    datatype CreateAwsKmsMrkKeyringInput = CreateAwsKmsMrkKeyringInput(
        nameonly kmsKeyId: KmsKeyId,
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly grantTokens: Option<GrantTokenList>
    )

    datatype CreateAwsKmsMrkMultiKeyringInput = CreateAwsKmsMrkMultiKeyringInput(
        nameonly generator: Option<KmsKeyId>,
        nameonly kmsKeyIds: Option<KmsKeyIdList>,
        nameonly clientSupplier: Option<IClientSupplier>,
        nameonly grantTokens: Option<GrantTokenList>
    )

    // KMS - MRK Aware, Discovery
    datatype CreateAwsKmsMrkDiscoveryKeyringInput = CreateAwsKmsMrkDiscoveryKeyringInput(
        nameonly kmsClient: KMS.IKeyManagementServiceClient,
        nameonly discoveryFilter: Option<DiscoveryFilter>,
        nameonly grantTokens: Option<GrantTokenList>,
        nameonly region: string
    )

    datatype CreateAwsKmsMrkDiscoveryMultiKeyringInput = CreateAwsKmsMrkDiscoveryMultiKeyringInput(
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

    trait {:termination false} IAwsCryptographicMaterialProvidersFactory {
        method CreateDefaultAwsCryptographicMaterialProviders()
            returns (res: Result<IAwsCryptographicMaterialProviders, IAwsCryptographicMaterialProvidersException>)
    }

    trait {:termination false} IAwsCryptographicMaterialProviders {

        // Keyrings
        method CreateAwsKmsKeyring(input: CreateAwsKmsKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsMultiKeyring(input: CreateAwsKmsMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsDiscoveryKeyring(input: CreateAwsKmsDiscoveryKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsDiscoveryMultiKeyring(input: CreateAwsKmsDiscoveryMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsMrkKeyring(input: CreateAwsKmsMrkKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsMrkMultiKeyring(input: CreateAwsKmsMrkMultiKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsMrkDiscoveryKeyring(input: CreateAwsKmsMrkDiscoveryKeyringInput)
            returns (res: Result<IKeyring, IAwsCryptographicMaterialProvidersException>)
        method CreateAwsKmsMrkDiscoveryMultiKeyring(input: CreateAwsKmsMrkDiscoveryMultiKeyringInput)
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

        // Client Supplier
        method CreateDefaultClientSupplier(input: CreateDefaultClientSupplierInput)
          returns (res: Result<IClientSupplier, IAwsCryptographicMaterialProvidersException>)
    }

    trait IAwsCryptographicMaterialProvidersException {
        function method GetMessage(): (message: string)
            reads this
    }

    class AwsCryptographicMaterialProvidersException extends IAwsCryptographicMaterialProvidersException {
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
                    var wrappedError := new AwsCryptographicMaterialProvidersException(error);
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
              var wrappedError := new AwsCryptographicMaterialProvidersException(error);
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
            var exception := new AwsCryptographicMaterialProvidersException(error);
            return Fail(exception);
        }
    }
}
