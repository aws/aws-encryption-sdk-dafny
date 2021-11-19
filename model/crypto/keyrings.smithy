namespace aws.crypto

use aws.polymorph#reference
use aws.polymorph#positional

resource Keyring {
    operations: [OnEncrypt, OnDecrypt]
}


/////////////////////
// Keyring Structures

@reference(resource: Keyring)
structure KeyringReference {}

list KeyringList {
    member: KeyringReference
}

structure DiscoveryFilter {
    @required
    region: String,

    @required
    partition: String
}

map EncryptionContext {
    key: Utf8Bytes,
    value: Utf8Bytes,
}

// Grant Tokens are base64 encoded strings
// https://docs.aws.amazon.com/kms/latest/developerguide/grants.html#grant_token
// We could theoretically put a @pattern trait here limited to base64 characters,
// but the actual Coral model/API docs for KMS don't include this constraint:
// https://docs.aws.amazon.com/kms/latest/APIReference/API_CreateGrant.html
// For now we'll mirror the API docs (generated from the model) and omit the pattern.
list GrantTokenList {
    member: String
}


/////////////////////
// Keyring Operations

operation OnEncrypt {
    input: OnEncryptInput,
    output: OnEncryptOutput,
}

structure OnEncryptInput {
    @required
    materials: EncryptionMaterials
}

structure OnEncryptOutput {
    @required
    materials: EncryptionMaterials
}

operation OnDecrypt {
    input: OnDecryptInput,
    output: OnDecryptOutput,
}

structure OnDecryptInput {
    @required
    materials: DecryptionMaterials,

    @required
    encryptedDataKeys: EncryptedDataKeyList
}

structure OnDecryptOutput {
    @required
    materials: DecryptionMaterials
}


///////////////////////
// Keyring Constructors

@positional
structure CreateKeyringOutput {
    keyring: KeyringReference
}

// TODO
// // KMS - Old Style
//
// operation CreateAwsKmsKeyring {
//     input: CreateAwsKmsKeyringInput,
//     output: CreateKeyringOutput 
// }
//
// structure CreateAwsKmsKeyringInput {
//     @required
//     clientSupplier: ClientSupplierReference,
//
//     // Not required because the keyring could be in discovery mode
//     generator: KmsKeyId,
//
//     keyIds: KmsKeyIdList,
//
//     grantTokens: GrantTokenList,
// }
//
// // KMS - MRK Aware, Strict
// operation CreateMrkAwareStrictAwsKmsKeyring {
//     input: CreateMrkAwareStrictAwsKmsKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateMrkAwareStrictAwsKmsKeyringInput {
//     @required
//     kmsKeyId: KmsKeyId,
//
//     @required
//     kmsClient: KmsClientReference,
//
//     grantTokens: GrantTokenList
// }
//
// operation CreateMrkAwareStrictMultiKeyring {
//     input: CreateMrkAwareStrictMultiKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateMrkAwareStrictMultiKeyringInput {
//     // TODO: spec doesn't call this required but it seems like it should be
//     generator:  KmsKeyId,
//
//     kmsKeyIds: KmsKeyIdList,
//
//     clientSupplier: ClientSupplierReference,
//
//     grantTokens: GrantTokenList
// }
//
// // KMS - MRK Aware, Discovery
//
// operation CreateMrkAwareDiscoveryAwsKmsKeyring {
//     input: CreateMrkAwareDiscoveryAwsKmsKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateMrkAwareDiscoveryAwsKmsKeyringInput {
//     @required
//     kmsClient: KmsClientReference,
//
//     discoveryFilter: DiscoveryFilter,
//
//     grantTokens: GrantTokenList
// }
//
// operation CreateMrkAwareDiscoveryMultiKeyring {
//     input: CreateMrkAwareDiscoveryMultiKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateMrkAwareDiscoveryMultiKeyringInput {
//     @required
//     regions: RegionList,
//
//     discoveryFilter: DiscoveryFilter,
//
//     clientSupplier: ClientSupplierReference,
//
//     grantTokens: GrantTokenList
// }

// TODO
// Multi
//
// operation CreateMultiKeyring {
//     input: CreateMultiKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateMultiKeyringInput {
//     generator: KeyringReference,
//     childKeyrings: KeyringList
// }

// Raw

operation CreateRawAesKeyring {
    input: CreateRawAesKeyringInput,
    output: CreateKeyringOutput,
}

structure CreateRawAesKeyringInput {
    @required
    keyNamespace: String,

    @required
    keyName: String,

    @required
    wrappingKey: Blob,

    @required
    wrappingAlg: AesWrappingAlg,
}

// TODO
// operation CreateRawRsaKeyring {
//     input: CreateRawRsaKeyringInput,
//     output: CreateKeyringOutput,
// }
//
// structure CreateRawRsaKeyringInput {
//     @required
//     keyNamespace: String,
//
//     @required
//     keyName: String,
//
//     @required
//     paddingScheme: PaddingScheme,
//
//     // One or both is required
//     publicKey: Blob,
//     privateKey: Blob
// }
