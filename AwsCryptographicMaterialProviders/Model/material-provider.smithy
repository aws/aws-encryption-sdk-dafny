namespace aws.cryptography.materialProviders

/////////////
// AwsCryptographicMaterialProviders Creation
@aws.polymorph#localService(
  sdkId: "MaterialProviders",
  config: MaterialProvidersConfig,
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

    // CMMs
    CreateDefaultCryptographicMaterialsManager,

    // ClientSupplier
    CreateDefaultClientSupplier,

    // Materials
    InitializeEncryptionMaterials,
    InitializeDecryptionMaterials,
    InitializeHierarchicalMaterials,
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
