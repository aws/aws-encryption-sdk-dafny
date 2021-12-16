namespace aws.crypto

use aws.polymorph#clientConfig

// TODO
// @clientConfig(config: AwsCryptographicMaterialProvidersClientConfig)
service AwsCryptographicMaterialProviders {
    version: "2021-11-01",
    resources: [
        Keyring,
        CryptographicMaterialsManager,
        CryptoMaterialsCache,
        // TODO
        // ClientSupplier,
    ],
    operations: [
        // Keyrings
        // TODO
        // CreateAwsKmsKeyring,
        CreateMrkAwareStrictAwsKmsKeyring,
        // CreateMrkAwareStrictMultiKeyring,
        // CreateMrkAwareDiscoveryAwsKmsKeyring,
        // CreateMrkAwareDiscoveryMultiKeyring,
        CreateMultiKeyring,
        CreateRawAesKeyring,
        // CreateRawRsaKeyring,

        // CMMs
        CreateDefaultCryptographicMaterialsManager,
        // TODO
        // CreateCachingCryptographicMaterialsManager,

        // Caches
        // TODO
        // CreateLocalCryptoMaterialsCache
    ]
}

structure AwsCryptographicMaterialProvidersClientConfig {
    @required
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
