namespace aws.crypto

use aws.polymorph#reference

/////////////
// AwsCryptographicMaterialProvidersClient Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
service AwsCryptographicMaterialProvidersClientFactory {
    version: "2021-11-01",
    operations: [MakeAwsCryptographicMaterialProvidersClient],
    errors: [AwsCryptographicMaterialProvidersClientException],
}

operation MakeAwsCryptographicMaterialProvidersClient {
    input: AwsCryptographicMaterialProvidersClientConfig,
    output: AwsCryptographicMaterialProvidersClientReference,
    errors: [AwsCryptographicMaterialProvidersClientException],
}

structure AwsCryptographicMaterialProvidersClientConfig {
    @required
    configDefaults: ConfigurationDefaults
}

@reference(resource: AwsCryptographicMaterialProvidersClient)
structure AwsCryptographicMaterialProvidersClientReference {}

///////////////////
// Default Versions

@enum([
    {
        name: "V1",
        value: "V1",
    }
])
string ConfigurationDefaults

/////////////
// AwsCryptographicMaterialProvidersClient

resource AwsCryptographicMaterialProvidersClient {
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


///////////////////
// Errors

@error("client")
structure AwsCryptographicMaterialProvidersClientException {
    @required
    message: String,
}
