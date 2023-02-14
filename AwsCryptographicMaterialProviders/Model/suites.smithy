namespace aws.cryptography.materialProviders

///////////////////////////////////
// Algorithm Suites

// For now, the actual properties of algorithm suites are only used by internal
// components and are not actually customer facing. If and when we make them
// customer facing, we will need to either model the AlgorithmSuiteProperties
// as a separate structure (with an associated resource/operation for translating
// from name to properties) or use more advanced custom traits which allow us to
// model all properties of the algorithm suite in one structure. 
@enum([
  {
    name: "ALG_AES_128_GCM_IV12_TAG16_NO_KDF",
    value: "0x0014",
  },
  {
    name: "ALG_AES_192_GCM_IV12_TAG16_NO_KDF",
    value: "0x0046",
  },
  {
    name: "ALG_AES_256_GCM_IV12_TAG16_NO_KDF",
    value: "0x0078",
  },
  {
    name: "ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256",
    value: "0x0114",
  },
  {
    name: "ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256",
    value: "0x0146",
  },
  {
    name: "ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256",
    value: "0x0178",
  },
  {
    name: "ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256",
    value: "0x0214",
  },
  {
    name: "ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384",
    value: "0x0346",
  },
  {
    name: "ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384",
    value: "0x0378",
  },
  {
    name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY",
    value: "0x0478",
  },
  {
    name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384",
    value: "0x0578",
  },
])
string ESDKAlgorithmSuiteId

@enum([
  {
    name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384",
    value: "0x6700",
  },
  {
    name: "ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384",
    value: "0x6701",
  },
])
string DBEAlgorithmSuiteId

//= aws-encryption-sdk-specification/framework/algorithm-suites.md#supported-algorithm-suites-enum
//= type=implication
//# The Material Providers Library MUST provide
//# an ENUM that is the super set of all the [supported format algorithm suites enum](#supported-format-algorithm-suites-enum)
//# called the Algorithm Suite ENUM.
//
//= aws-encryption-sdk-specification/framework/algorithm-suites.md#supported-algorithm-suites-enum
//= type=implication
//# This means that different formats MAY have duplicate Format Algorithm Suite ENUM.
//
//= aws-encryption-sdk-specification/framework/algorithm-suites.md#overview
//= type=implication
//# The algorithm suite defines the behaviors [supported formats](#supported-formats) MUST follow for cryptographic operations.
union AlgorithmSuiteId {
  ESDK: ESDKAlgorithmSuiteId,
  DBE: DBEAlgorithmSuiteId,
}

//= aws-encryption-sdk-specification/framework/algorithm-suites.md#structure
//= type=implication
//# The fields described below are REQUIRED to be specified by algorithm suites, unless otherwise specified.
structure AlgorithmSuiteInfo {
  @required
  id: AlgorithmSuiteId,
  @required
  binaryId: Blob,
  @required
  messageVersion: Integer,
  @required
  encrypt: Encrypt,
  @required
  kdf: DerivationAlgorithm,
  @required
  commitment: DerivationAlgorithm,
  @required
  signature: SignatureAlgorithm,
  @required
  symmetricSignature: SymmetricSignatureAlgorithm,
  @required
  edkWrapping: EdkWrappingAlgorithm
}
 
union Encrypt {
  //= aws-encryption-sdk-specification/framework/algorithm-suites.md#gcm
  //= type=implication
  //# If specified to use GCM, the AWS Encryption SDK MUST use GCM with the following specifics:
  //# - The internal block cipher is the encryption algorithm specified by the algorithm suite.
  AES_GCM: aws.cryptography.primitives#AES_GCM,
}

union DerivationAlgorithm {
  HKDF: HKDF,
  // We are using both `IDENTITY` and `None` here
  // to modle the fact that deriving
  // the data encryption key and the commitment key
  // MUST be the same.
  // The specification treats NO_KDF as an identity operation.
  // So this naming convention mirrors the specification.
  IDENTITY: IDENTITY,
  None: None,
}

//= aws-encryption-sdk-specification/framework/algorithm-suites.md#asymmetric-signature-algorithm
//= type=implication
//# This field is OPTIONAL.
union SignatureAlgorithm {
  ECDSA: ECDSA,
  None: None
}

structure HKDF {
  @required
  hmac: aws.cryptography.primitives#DigestAlgorithm,
  @required
  saltLength: aws.cryptography.primitives#PositiveInteger,
  @required
  inputKeyLength: aws.cryptography.primitives#SymmetricKeyLength,
  @required
  outputKeyLength: aws.cryptography.primitives#SymmetricKeyLength,
}
structure IDENTITY {}
structure None {}

structure ECDSA {
  @required
  curve: aws.cryptography.primitives#ECDSASignatureAlgorithm,
}

//= aws-encryption-sdk-specification/framework/algorithm-suites.md#symmetric-signature-algorithm
//# This field is OPTIONAL.
union SymmetricSignatureAlgorithm {
  HMAC: aws.cryptography.primitives#DigestAlgorithm,
  None: None
}

union EdkWrappingAlgorithm {
  DIRECT_KEY_WRAPPING: DIRECT_KEY_WRAPPING,
  IntermediateKeyWrapping: IntermediateKeyWrapping,
}

structure DIRECT_KEY_WRAPPING {}

structure IntermediateKeyWrapping {
  @required
  keyEncryptionKeyKdf: DerivationAlgorithm,
  @required
  macKeyKdf: DerivationAlgorithm,
  @required
  pdkEncryptAlgorithm: Encrypt
}

@readonly
operation GetAlgorithmSuiteInfo {
  input: GetAlgorithmSuiteInfoInput,
  output: AlgorithmSuiteInfo,
}

@aws.polymorph#positional
structure GetAlgorithmSuiteInfoInput {
  @required
  binaryId: Blob
}

@readonly
operation ValidAlgorithmSuiteInfo {
  input: AlgorithmSuiteInfo,
  errors: [InvalidAlgorithmSuiteInfo]
}

@error("client")
structure InvalidAlgorithmSuiteInfo {
  @required
  message: String,
}
