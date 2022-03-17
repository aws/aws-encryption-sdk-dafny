namespace aws.encryptionSdk.core

use aws.polymorph#reference

/////////////
// AwsCryptographicMaterialProviders Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
service AwsCryptographicMaterialProvidersFactory {
    version: "2021-11-01",
    operations: [CreateDefaultAwsCryptographicMaterialProviders],
    errors: [AwsCryptographicMaterialProvidersException],
}

operation CreateDefaultAwsCryptographicMaterialProviders {
    output: AwsCryptographicMaterialProvidersReference,
    errors: [AwsCryptographicMaterialProvidersException],
}

@reference(resource: AwsCryptographicMaterialProviders)
structure AwsCryptographicMaterialProvidersReference {}

/////////////
// AwsCryptographicMaterialProviders

resource AwsCryptographicMaterialProviders {
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
structure AwsCryptographicMaterialProvidersException {
    @required
    message: String,
}
