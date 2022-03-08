namespace aws.crypto

use aws.polymorph#clientConfig

// TODO
// @clientConfig(config: AwsCryptographicMaterialProvidersClientConfig)
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
        CreateMultiKeyring,
        CreateRawAesKeyring,
        CreateRawRsaKeyring,

        // CMMs
        CreateDefaultCryptographicMaterialsManager,

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
