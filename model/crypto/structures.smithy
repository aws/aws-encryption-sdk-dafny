namespace aws.encryptionSdk.core

use aws.polymorph#dafnyUtf8Bytes

@dafnyUtf8Bytes
string Utf8Bytes

///////////////////////////////////
// Encryption Materials 

// In the future, we have several improvements we can consider here:
//   1. Model these materials structures as resources, in order to move towards "smarter"
//      materials. This would allow us to tightly define the valid interactions with
//      materials and prevent dangerous or unexpected uses of them. 
//   2. Use different materials structures for keyrings and CMMs. These live at
//      different layers of the library and have different needs and responsibilities,
//      so we may eventually want to give them each materials specialized to their
//      purpose.
// Note that both of these will be breaking changes to any customers building
// custom implementations of keyrings or CMMs.
structure EncryptionMaterials {
    @required
    algorithmSuiteId: AlgorithmSuiteId,

    @required
    encryptionContext: EncryptionContext,

    @required
    encryptedDataKeys: EncryptedDataKeyList,

    @sensitive
    plaintextDataKey: Blob,

    @sensitive
    signingKey: Blob
}

structure DecryptionMaterials {
    @required
    algorithmSuiteId: AlgorithmSuiteId,

    @required
    encryptionContext: EncryptionContext,

    @sensitive
    plaintextDataKey: Blob,

    @sensitive
    verificationKey: Blob
}

structure EncryptedDataKey {
    // The spec defines keyProviderId in 2 places,
    // and, while they are not identical,
    // they do not disagree.
    // data-format/message-header.md#encrypted-data-key-entries ::
    // UTF-8 encoded bytes
    // framework/keyring-interface.md#key-provider-id ::
    // The key provider ID MUST be a binary value and SHOULD be equal to a UTF-8 encoding of the key namespace.
    @required
    keyProviderId: Utf8Bytes,

    // The key provider info MUST be a binary value and SHOULD be equal to a UTF-8 encoding of the key name.
    @required
    keyProviderInfo: Blob,

    @required
    ciphertext: Blob
}

list EncryptedDataKeyList {
    member: EncryptedDataKey
}


