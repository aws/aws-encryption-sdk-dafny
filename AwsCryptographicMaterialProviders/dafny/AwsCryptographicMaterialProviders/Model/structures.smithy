namespace aws.cryptography.materialProviders

use aws.polymorph#dafnyUtf8Bytes

@dafnyUtf8Bytes
string Utf8Bytes

//= aws-encryption-sdk-specification/framework/structures.md#overview
//= type=implication
//# While these structures will usually be represented as objects, lower level languages MAY represent
//# these fields in a less strictly defined way as long as all field properties are still upheld.

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

//= aws-encryption-sdk-specification/framework/structures.md#structure-2
//= type=implication
//# This structure MUST include the following fields:
//# 
//# - [Algorithm Suite](#algorithm-suite)
//# - [Encrypted Data Keys](#encrypted-data-keys)
//# - [Encryption Context](#encryption-context-1)
//# - [Required Encryption Context Keys](#required-encryption-context-keys)

  @required
  algorithmSuite: AlgorithmSuiteInfo,

  @required
  encryptionContext: EncryptionContext,

  @required
  encryptedDataKeys: EncryptedDataKeyList,

  @required
  requiredEncryptionContextKeys: EncryptionContextKeys,

//= aws-encryption-sdk-specification/framework/structures.md#structure-2
//= type=implication
//# This structure MAY include any of the following fields:
//# 
//# - [Plaintext Data Key](#plaintext-data-key)
//# - [Signing Key](#signing-key)

  plaintextDataKey: Secret,

  signingKey: Secret,

  symmetricSigningKeys: SymmetricSigningKeyList
}

structure DecryptionMaterials {
  //= aws-encryption-sdk-specification/framework/structures.md#fields
  //= type=implication
  //# This structure MUST include the following fields:
  //# 
  //# - [Algorithm Suite](#algorithm-suite-1)
  //# - [Encryption Context](#encryption-context-2)
  //# - [Required Encryption Context Keys](#required-encryption-context-keys-1)

  @required
  algorithmSuite: AlgorithmSuiteInfo,

  @required
  encryptionContext: EncryptionContext,

  @required
  requiredEncryptionContextKeys: EncryptionContextKeys,

  //= aws-encryption-sdk-specification/framework/structures.md#fields
  //= type=implication
  //# This structure MAY include any of the following fields:
  //# 
  //# - [Plaintext Data Key](#plaintext-data-key-1)
  //# - [Verification Key](#verification-key)

  plaintextDataKey: Secret,

  verificationKey: Secret,

  //= aws-encryption-sdk-specification/framework/structures.md#symmetric-signing-key
  //= type=implication
  //# This value MUST be kept secret.
  symmetricSigningKey: Secret
}

structure BranchKeyMaterials {
    @required
    branchKeyVersion: Utf8Bytes,

    @required 
    branchKey: Secret
}

structure BeaconKeyMaterials {
  //= aws-encryption-sdk-specification/framework/structures.md#structure-4
  //= type=implication
  //# This structure MUST include the following fields:
  //# - [Beacon Key Id](#beacon-key-id)
  @required
  beaconKeyIdentifier: String,

  //= aws-encryption-sdk-specification/framework/structures.md#structure-4
  //= type=implication
  //# This structure MAY include the following fields:
  //# - [Beacon Key](#beacon-key)
  //# - [HMAC Keys](#hmac-keys)

  beaconKey: Secret,

  hmacKeys: HmacKeyMap  
}


//= aws-encryption-sdk-specification/framework/structures.md#structure
//= type=implication
//# An encrypted data key is comprised of the following fields:
//# 
//# - [Key Provider ID](#key-provider-id)
//# - [Key Provider Information](#key-provider-information)
//# - [Ciphertext](#ciphertext)
//# 
//# Note: "Encrypted" is a misnomer here, as the process by which a key provider may obtain the plaintext data key
//# from the ciphertext and vice versa does not have to be an encryption and decryption cipher.
//# This specification uses the terms "encrypt" and "decrypt" for simplicity,
//# but the actual process by which a key provider obtains the plaintext data key from the ciphertext
//# and vice versa MAY be any reversible operation, though we expect that most will use encryption.
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

list EncryptionContextKeys {
  member: Utf8Bytes
}

list SymmetricSigningKeyList {
  //= aws-encryption-sdk-specification/framework/structures.md#symmetric-signing-keys
  //= type=implication
  //# The value of keys in this list MUST be kept secret.
  member: Secret
}

map HmacKeyMap {
  // This key refers to the beacon name for which this value was derived.
  key: String,
  // HKDF derived from the beacon key and the UTF Encoding of the beacon name.
  value: Secret
}

//= aws-encryption-sdk-specification/framework/structures.md#structure-1
//= type=implication
//# The encryption context is a key-value mapping of arbitrary, non-secret, UTF-8 encoded strings.
//# It is used during [encryption](../client-apis/encrypt.md) and [decryption](../client-apis/decrypt.md) to provide additional authenticated data (AAD).
map EncryptionContext {
  key: Utf8Bytes,
  value: Utf8Bytes,
}

@sensitive
blob Secret
