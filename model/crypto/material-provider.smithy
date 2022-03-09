namespace aws.crypto

use aws.polymorph#reference

/////////////
// AwsCryptographicMaterialProvidersClient Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
service AwsCryptographicMaterialProvidersClientFactory {
    version: "2021-11-01",
    operations: [CreateDefaultAwsCryptographicMaterialProvidersClient],
    errors: [AwsCryptographicMaterialProvidersClientException],
}

operation CreateDefaultAwsCryptographicMaterialProvidersClient {
    output: AwsCryptographicMaterialProvidersClientReference,
    errors: [AwsCryptographicMaterialProvidersClientException],
}

@reference(resource: AwsCryptographicMaterialProvidersClient)
structure AwsCryptographicMaterialProvidersClientReference {}

/////////////
// AwsCryptographicMaterialProvidersClient

resource AwsCryptographicMaterialProvidersClient {
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


///////////////////
// Errors

@error("client")
structure AwsCryptographicMaterialProvidersClientException {
    @required
    message: String,
}
