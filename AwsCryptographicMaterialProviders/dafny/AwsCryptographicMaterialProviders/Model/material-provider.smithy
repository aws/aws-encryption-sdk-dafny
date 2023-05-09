namespace aws.cryptography.materialProviders

use aws.cryptography.keyStore#KeyStore
use aws.cryptography.primitives#AwsCryptographicPrimitives
use com.amazonaws.dynamodb#DynamoDB_20120810
use com.amazonaws.kms#TrentService

@range(min: 0)
integer PositiveInteger

@range(min: 0)
long PositiveLong

/////////////
// AwsCryptographicMaterialProviders Creation
@aws.polymorph#localService(
  sdkId: "MaterialProviders",
  config: MaterialProvidersConfig,
  dependencies: [
    AwsCryptographicPrimitives,
    DynamoDB_20120810,
    TrentService,
    KeyStore
  ]
)
service AwsCryptographicMaterialProviders {
  version: "2021-11-01",
  resources: [
    Keyring,
    CryptographicMaterialsManager,
    ClientSupplier,
  ],
  operations: [
    // Keyrings
    CreateAwsKmsKeyring,
    CreateAwsKmsDiscoveryKeyring,
    CreateAwsKmsMultiKeyring,
    CreateAwsKmsDiscoveryMultiKeyring,
    CreateAwsKmsMrkKeyring,
    CreateAwsKmsMrkMultiKeyring,
    CreateAwsKmsMrkDiscoveryKeyring,
    CreateAwsKmsMrkDiscoveryMultiKeyring,
    CreateAwsKmsHierarchicalKeyring,
    CreateMultiKeyring,
    CreateRawAesKeyring,
    CreateRawRsaKeyring,
    CreateAwsKmsRsaKeyring,

    // CMMs
    CreateDefaultCryptographicMaterialsManager,
    CreateExpectedEncryptionContextCMM,

    // CMCs
    CreateCryptographicMaterialsCache,

    // ClientSupplier
    CreateDefaultClientSupplier,

    // Materials
    InitializeEncryptionMaterials,
    InitializeDecryptionMaterials,
    ValidEncryptionMaterialsTransition,
    ValidDecryptionMaterialsTransition,
    EncryptionMaterialsHasPlaintextDataKey,
    DecryptionMaterialsWithPlaintextDataKey,

    // AlgorithmSuiteInfo
    GetAlgorithmSuiteInfo,
    ValidAlgorithmSuiteInfo,

    // Commitment
    ValidateCommitmentPolicyOnEncrypt,
    ValidateCommitmentPolicyOnDecrypt,
  ],
  errors: [AwsCryptographicMaterialProvidersException],
}

structure MaterialProvidersConfig {}

///////////////////
// Errors

@error("client")
structure AwsCryptographicMaterialProvidersException {
  @required
  message: String,
}
