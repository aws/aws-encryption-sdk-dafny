namespace aws.crypto

use aws.polymorph#clientConfig

@clientConfig(config: AwsCryptographicMaterialProvidersClientConfig)
service AwsCryptographicMaterialProviders {
    version: "2021-11-01",
    resources: [Keyring, CryptographicMaterialsManager, CryptoMaterialsCache, ClientSupplier],
    operations: [
        // Keyrings
        CreateAwsKmsKeyring,
        CreateMrkAwareStrictAwsKmsKeyring,
        CreateMrkAwareStrictMultiKeyring,
        CreateMrkAwareDiscoveryAwsKmsKeyring,
        CreateMrkAwareDiscoveryMultiKeyring,
        CreateMultiKeyring,
        CreateRawAesKeyring,
        CreateRawRsaKeyring,

        // CMMs
        CreateDefaultCryptographicMaterialsManager,
        CreateCachingCryptographicMaterialsManager,

        // Caches
        CreateLocalCryptoMaterialsCache
    ]
}

structure AwsCryptographicMaterialProvidersClientConfig {
    configDefaults: ConfigurationDefaults
}

///////////////////
// Default Versions

@enum([
    {
        name: "V1",
        value: "V1",
    }
])
string ConfigurationDefaults
