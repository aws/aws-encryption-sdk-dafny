namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable

use com.amazonaws.kms#EncryptionAlgorithmSpec

@extendable
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
  accountIds: AccountIdList,

  @required
  partition: String
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

//= aws-encryption-sdk-specification/framework/keyring-interface.md#onencrypt
//= type=implication
//# This interface MUST take [encryption materials](structures.md#encryption-materials) as input.
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

//= aws-encryption-sdk-specification/framework/keyring-interface.md#ondecrypt
//= type=implication
//# This interface MUST take [decryption materials](structures.md#decryption-materials) and
//# a list of [encrypted data keys](structures.md#encrypted-data-key) as input.
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
  @required
  keyring: KeyringReference
}

// KMS - Strict
operation CreateAwsKmsKeyring {
  input: CreateAwsKmsKeyringInput,
  output: CreateKeyringOutput
}
structure CreateAwsKmsKeyringInput {
  @required
  kmsKeyId: KmsKeyId,

  @required
  kmsClient: KmsClientReference,

  grantTokens: GrantTokenList
}

operation CreateAwsKmsMultiKeyring {
  input: CreateAwsKmsMultiKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsMultiKeyringInput {
  generator:  KmsKeyId,

  kmsKeyIds: KmsKeyIdList,

  clientSupplier: ClientSupplierReference,

  grantTokens: GrantTokenList
}

// KMS - Discovery
operation CreateAwsKmsDiscoveryKeyring {
  input: CreateAwsKmsDiscoveryKeyringInput,
  output: CreateKeyringOutput
}

structure CreateAwsKmsDiscoveryKeyringInput {
  @required
  kmsClient: KmsClientReference,

  discoveryFilter: DiscoveryFilter,

  grantTokens: GrantTokenList
}

operation CreateAwsKmsDiscoveryMultiKeyring {
  input: CreateAwsKmsDiscoveryMultiKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsDiscoveryMultiKeyringInput {
  @required
  regions: RegionList,

  discoveryFilter: DiscoveryFilter,

  clientSupplier: ClientSupplierReference,

  grantTokens: GrantTokenList
}

// KMS - MRK Aware, Strict
operation CreateAwsKmsMrkKeyring {
  input: CreateAwsKmsMrkKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsMrkKeyringInput {
  @required
  kmsKeyId: KmsKeyId,

  @required
  kmsClient: KmsClientReference,

  grantTokens: GrantTokenList
}

operation CreateAwsKmsMrkMultiKeyring {
  input: CreateAwsKmsMrkMultiKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsMrkMultiKeyringInput {
  generator:  KmsKeyId,

  kmsKeyIds: KmsKeyIdList,

  clientSupplier: ClientSupplierReference,

  grantTokens: GrantTokenList
}

// KMS - MRK Aware, Discovery

operation CreateAwsKmsMrkDiscoveryKeyring {
  input: CreateAwsKmsMrkDiscoveryKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsMrkDiscoveryKeyringInput {
  @required
  kmsClient: KmsClientReference,

  discoveryFilter: DiscoveryFilter,

  grantTokens: GrantTokenList,

  @required // TODO: probably shouldn't be
  region: Region
}

operation CreateAwsKmsMrkDiscoveryMultiKeyring {
  input: CreateAwsKmsMrkDiscoveryMultiKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateAwsKmsMrkDiscoveryMultiKeyringInput {
  @required
  regions: RegionList,

  discoveryFilter: DiscoveryFilter,

  clientSupplier: ClientSupplierReference,

  grantTokens: GrantTokenList
}

// TODO
// Multi

operation CreateMultiKeyring {
  input: CreateMultiKeyringInput,
  output: CreateKeyringOutput,
}

structure CreateMultiKeyringInput {
  generator: KeyringReference,

  // We'll represent "no children" as an empty list
  @required
  childKeyrings: KeyringList
}

// KMS - Hierarchical Keyring
operation CreateAwsKmsHierarchicalKeyring {
    input: CreateAwsKmsHierarchicalKeyringInput,
    output: CreateKeyringOutput,
}

@extendable
resource BranchKeyIdSupplier {
  operations: [GetBranchKeyId],
}

@reference(resource: BranchKeyIdSupplier)
structure BranchKeyIdSupplierReference {}

operation GetBranchKeyId {
  input: GetBranchKeyIdInput,
  output: GetBranchKeyIdOutput
}

structure GetBranchKeyIdInput {
  @required
  encryptionContext: EncryptionContext
}

structure GetBranchKeyIdOutput {
  @required
  branchKeyId: String
}

structure CreateAwsKmsHierarchicalKeyringInput {
    // branchKeyId XOR BranchKeyIdSupplier required
    branchKeyId: String,
    branchKeyIdSupplier: BranchKeyIdSupplierReference,

    @required
    kmsKeyId: KmsKeyId,

    @required
    keyStore: KeyStoreReference,
    
    @required
    ttlSeconds: PositiveLong,

    maxCacheSize: PositiveInteger,

    grantTokens: GrantTokenList
}

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

 operation CreateRawRsaKeyring {
   input: CreateRawRsaKeyringInput,
   output: CreateKeyringOutput,
 }

 structure CreateRawRsaKeyringInput {
   @required
   keyNamespace: String,

   @required
   keyName: String,

   @required
   paddingScheme: PaddingScheme,

   // One or both is required
   publicKey: Blob,
   privateKey: Blob
 }

  operation CreateAwsKmsRsaKeyring {
    input: CreateAwsKmsRsaKeyringInput,
    output: CreateKeyringOutput,
  }

  structure CreateAwsKmsRsaKeyringInput {
    // MUST be configured for this keyring to allow encryption
    publicKey: Secret,
    @required
    kmsKeyId: KmsKeyId,
    @required
    encryptionAlgorithm: EncryptionAlgorithmSpec,
    // MUST be configured for this keyring to allow decryption
    kmsClient: KmsClientReference,
    grantTokens: GrantTokenList
  }
