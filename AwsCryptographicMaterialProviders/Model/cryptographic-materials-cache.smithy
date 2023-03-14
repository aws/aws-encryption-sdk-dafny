namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable

@aws.polymorph#mutableLocalState
@aws.polymorph#extendable
resource CryptographicMaterialsCache {

  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#overview
  //= type=implication
  //# Cryptographic materials cache (CMC) is used by the [caching cryptographic materials manager (CMM)](caching-cmm.md)
  //# to store cryptographic materials for reuse.
  //# This document describes the interface that all CMCs MUST implement.
  operations: [PutCacheEntry, GetCacheEntry, UpdaterUsageMetadata, DeleteCacheEntry]
}

@aws.polymorph#reference(resource: CryptographicMaterialsCache)
structure CryptographicMaterialsCacheReference {}

//= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#put-cache-entry
//= type=implication
//# This operation MUST NOT return the inserted cache entry.
operation PutCacheEntry {
  input: PutCacheEntryInput,
}

structure PutCacheEntryInput {
  @required
  identifier: Blob,
  @required
  materials: Materials,
  @required
  creationTime: PositiveLong,
  @required
  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#put-cache-entry
  //= type=implication
  //# The cache entry MUST include all [usage metadata](#usage-metadata)
  //# since this information can not be updated after the put operation.
  expiryTime: PositiveLong,
  messagesUsed: PositiveLong,
  bytesUsed: PositiveLong,
}

operation GetCacheEntry {
  input: GetCacheEntryInput,
  output: GetCacheEntryOutput,
}

structure GetCacheEntryInput {
  @required
  identifier: Blob,
  bytesUsed: Long

}

//= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#cache-entry
//= type=implication
//# A cache entry represents an entry in the cryptographic materials cache
//# and MUST have the following information.
//# 
//# - [Materials](#materials)
//# - [Creation Time](#creation-time)
//# - [Expiry Time](#expiry-time)
//# - [Usage Metadata](#usage-metadata)
structure GetCacheEntryOutput {
  @required
  materials: Materials,
  @required
  creationTime: PositiveLong,
  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#time-to-live-ttl
  //= type=implication
  //# Each cache entry has a time-to-live (TTL)
  //# that represents a point in time at which the cache entry
  //# MUST be considered invalid.
  @required
  expiryTime: PositiveLong,
  @required
  messagesUsed: PositiveLong,
  @required
  bytesUsed: PositiveLong,
}

union Materials {
  Encryption: EncryptionMaterials,
  Decryption: DecryptionMaterials,
  Hierarchical: HierarchicalMaterials,
}

operation DeleteCacheEntry {
  input: DeleteCacheEntryInput
}

structure DeleteCacheEntryInput {
  @required
  identifier: Blob
}

operation UpdaterUsageMetadata {
  input: UpdaterUsageMetadataInput
}

structure UpdaterUsageMetadataInput {
  @required
  identifier: Blob,
  @required
  bytesUsed: PositiveLong,
}

@error("client")
structure EntryDoesNotExist {
  @required
  message: String,
}

@error("client")
structure EntryAlreadyExists {
  @required
  message: String,
}

@range(min: 0)
integer PositiveLong

///////////////////
// Materials Cache Constructors

@positional
structure CreateCryptographicMaterialsCacheOutput {
  @required
  materialsCache: CryptographicMaterialsCacheReference 
}

operation CreateCryptographicMaterialsCache {
  input: CreateCryptographicMaterialsCacheInput,
  output: CreateCryptographicMaterialsCacheOutput,
}

structure CreateCryptographicMaterialsCacheInput {
  //= aws-encryption-sdk-specification/framework/local-cryptographic-materials-cache.md#initialization
  //= type=implication
  //# On initialization of the local CMC,
  //# the caller MUST provide the following:
  //# 
  //# - [Entry Capacity](#entry-capacity)
  //# 
  //# The local CMC MUST also define the following:
  //# 
  //# - [Entry Pruning Tail Size](#entry-pruning-tail-size)
  @required
  @range(min: 0)
  entryCapacity: PositiveLong,

  @range(min: 0)
  entryPruningTailSize: PositiveLong, 
}
