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
        ClientSupplier,
    ],
    operations: [
        // Keyrings
        CreateStrictAwsKmsKeyring,
        CreateAwsKmsDiscoveryKeyring,
        CreateStrictAwsKmsMultiKeyring,
        CreateAwsKmsDiscoveryMultiKeyring,
        CreateMrkAwareStrictAwsKmsKeyring,
        CreateMrkAwareStrictMultiKeyring,
        CreateMrkAwareDiscoveryAwsKmsKeyring,
        CreateMrkAwareDiscoveryMultiKeyring,
        CreateMultiKeyring,
        CreateRawAesKeyring,
        CreateRawRsaKeyring,

        // CMMs
        CreateDefaultCryptographicMaterialsManager,
        // TODO
        // CreateCachingCryptographicMaterialsManager,

        // Caches
        // TODO
        // CreateLocalCryptoMaterialsCache,

        // ClientSupplier
        CreateDefaultClientSupplier
    ]
}

structure AwsCryptographicMaterialProvidersClientConfig {
    @required
    configDefaults: ConfigurationDefaults
}

@error("client")
structure AwsCryptographicMaterialProvidersClientException {
    @required
    message: String,
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
