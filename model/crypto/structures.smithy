namespace aws.crypto

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
    algorithm: AlgorithmSuite,

    encryptionContext: EncryptionContext,

    encryptedDataKeys: EncryptedDataKeyList,

    @sensitive
    plaintextDataKey: Blob,

    @sensitive
    signingKey: Blob
}

structure DecryptionMaterials {
    algorithm: AlgorithmSuite,

    encryptionContext: EncryptionContext,

    @sensitive
    plaintextDataKey: Blob,

    @sensitive
    verificationKey: Blob
}

structure EncryptedDataKey {
    @required
    keyProviderId: String,

    @required
    keyProviderInformation: String,

    @required
    cipherText: Blob
}

list EncryptedDataKeyList {
    member: EncryptedDataKey
}


