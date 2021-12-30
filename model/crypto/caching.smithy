namespace aws.crypto

use aws.polymorph#reference
use aws.polymorph#positional

// We model the cache as a resource so that we can clearly define its interface.
// Though the ESDK provides a built-in cache, customers may want the option to
// build a custom implementation of this interface.
resource CryptoMaterialsCache {
    operations: [PutEntryForEncrypt,
                 GetEntryForEncrypt,
                 PutEntryForDecrypt,
                 GetEntryForDecrypt,
                 DeleteEntry]
}

@reference(resource: CryptoMaterialsCache)
structure CryptoMaterialsCacheReference {}

@positional
structure CreateLocalCryptoMaterialsCacheOutput {
    cache: CryptoMaterialsCacheReference
}

operation CreateLocalCryptoMaterialsCache {
    input: CreateLocalCryptoMaterialsCacheInput,
    output: CreateLocalCryptoMaterialsCacheOutput,
}

structure CreateLocalCryptoMaterialsCacheInput {
    @required
    entryCapacity: Integer,

    entryPruningTailSize: Integer,
}

structure CacheUsageMetadata {
    @required
    messageUsage: Long,

    @required
    byteUsage: Long,
}

//////////
// Encrypt

structure EncryptEntry {
    @required
    identifier: Blob,

    @required
    encryptionMaterials: EncryptionMaterials,

    @required
    creationTime: Long,

    @required
    expiryTime: Long,

    @required
    usageMetadata: CacheUsageMetadata,
}

operation PutEntryForEncrypt {
    input: PutEntryForEncryptInput,
    output: PutEntryForEncryptOutput,
}

structure PutEntryForEncryptInput {
    @required
    identifier: Blob,

    @required
    encryptionMaterials: EncryptionMaterials,

    @required
    usageMetadata: CacheUsageMetadata,
}

structure PutEntryForEncryptOutput {
    // No output for now
}


operation GetEntryForEncrypt {
    input: GetEntryForEncryptInput,
    output: GetEntryForEncryptOutput,
}

structure GetEntryForEncryptInput {
    @required
    identifier: Blob,
}

structure GetEntryForEncryptOutput {
    @required
    cacheEntry: EncryptEntry,
}


//////////
// Decrypt

structure DecryptEntry {
    @required
    identifier: Blob,

    @required
    decryptionMaterials: DecryptionMaterials,

    @required
    creationTime: Long,

    @required
    expiryTime: Long,

    @required
    usageMetadata: CacheUsageMetadata,
}

operation PutEntryForDecrypt {
    input: PutEntryForDecryptInput,
    output: PutEntryForDecryptOutput,
}

structure PutEntryForDecryptInput {
    @required
    identifier: Blob,

    @required
    decryptionMaterials: DecryptionMaterials
}

structure PutEntryForDecryptOutput {
    // No output for now
}


operation GetEntryForDecrypt {
    input: GetEntryForDecryptInput,
    output: GetEntryForDecryptOutput,
}

structure GetEntryForDecryptInput {
    @required
    identifier: Blob,
}

structure GetEntryForDecryptOutput {
    @required
    cacheEntry: DecryptEntry,
}


/////////
// Delete

// Delete does not need separate APIs for encrypt/decrypt
operation DeleteEntry {
    input: DeleteEntryInput,
    output: DeleteEntryOutput,
}

structure DeleteEntryInput {
    @required
    identifier: Blob,
}

structure DeleteEntryOutput {
    // No output for now
}
