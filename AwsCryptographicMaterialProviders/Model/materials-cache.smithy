namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#dafnyUtf8Bytes

///////////////////
// Materials Cache
resource MaterialsCache {
    operations: [
        EvictEntry,
        GetMaterials,
        AddMaterials,
        ClearCache
    ]
}

structure MaterialsCacheConfig {
    @required
    @range(min: 1)
    maxCacheSize: Integer,

    @required
    @range(min: 1)
    ttlMilliseconds: Long
}

operation EvictEntry {
    input: EvictEntryInput,
    output: EvictEntryOutput
}

structure EvictEntryInput {
    @required
    key: Utf8Bytes,
}

structure EvictEntryOutput {
}

@readonly
operation GetMaterials {
    input: GetMaterialsInput,
    output: GetMaterialsOutput
}

structure GetMaterialsInput {
    @required
    key: Utf8Bytes,
}

structure GetMaterialsOutput {
    @required
    value: CachedMaterials
}

operation AddMaterials {
    input: AddMaterialsInput,
    output: AddMaterialsOutput
}

structure AddMaterialsInput {
    @required
    key: Utf8Bytes,

    @required
    value: CachedMaterials
}

structure AddMaterialsOutput {
}

operation ClearCache {
    input: ClearCacheInput,
    output: ClearCacheOutput
}

structure ClearCacheInput {
}

structure ClearCacheOutput {
}

union CachedMaterials {
    encryptionMaterials: EncryptionMaterials,

    decryptionMaterials: DecryptionMaterials,

    hierarchicalMaterials: HierarchicalMaterials
}
