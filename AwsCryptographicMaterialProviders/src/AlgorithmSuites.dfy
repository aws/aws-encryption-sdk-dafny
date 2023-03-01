// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AlgorithmSuites {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened AwsCryptographyMaterialProvidersTypes
  import Wrappers

  // Invariants for ESDK Encrypt
  predicate method SupportedESDKEncrypt?(e: Encrypt) {
    && e.AES_GCM?
    && (
      || e.AES_GCM.keyLength == 32
      || e.AES_GCM.keyLength == 24
      || e.AES_GCM.keyLength == 16)
    && e.AES_GCM.tagLength == 16
    && e.AES_GCM.ivLength == 12
  }

  // Invariants for DBE Encrypt
  predicate method SupportedDBEEncrypt?(e: Encrypt) {
    && e.AES_GCM?
    && e.AES_GCM.keyLength == 32
    && e.AES_GCM.tagLength == 16
    && e.AES_GCM.ivLength == 12
  }

  // Invariants for DBE EDK Wrapping Algorithms
  predicate method SupportedDBEEDKWrapping?(p: EdkWrappingAlgorithm) {
    && p.IntermediateKeyWrapping?
    && p.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM?
    && p.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.keyLength == 32
    && p.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.tagLength == 16
    && p.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.ivLength == 12
    && p.IntermediateKeyWrapping.macKeyKdf.HKDF?
    && p.IntermediateKeyWrapping.keyEncryptionKeyKdf.HKDF?
  }

  // Invariants for all supported KDFs
  predicate method KeyDerivationAlgorithm?(kdf: DerivationAlgorithm) {
    && (
        && kdf.HKDF?
      ==>
        && kdf.HKDF.inputKeyLength == kdf.HKDF.outputKeyLength
        && (kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512 ==> kdf.HKDF.inputKeyLength == 32))
    && !kdf.None?
  }

  // Invariants for all supported Commitment Derivation Algorithms
  predicate method CommitmentDerivationAlgorithm?(kdf: DerivationAlgorithm) {
    && (
        && kdf.HKDF?
      ==>
        && kdf.HKDF.hmac.SHA_512?
        && kdf.HKDF.saltLength == 32
        && kdf.HKDF.inputKeyLength == 32
        && kdf.HKDF.outputKeyLength == 32)
    && !kdf.IDENTITY?
  }

  // Invariants for all supported Provider Wrapping Algorithms
  predicate method EdkWrappingAlgorithm?(alg: EdkWrappingAlgorithm) {
    || (
        && alg.IntermediateKeyWrapping?
        && alg.IntermediateKeyWrapping.keyEncryptionKeyKdf.HKDF?
        && alg.IntermediateKeyWrapping.macKeyKdf.HKDF?
        && alg.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM?
        && alg.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.keyLength == 32
    )
    || alg.DIRECT_KEY_WRAPPING?
  }

  // Invariants for all supported Algorithm Suites
  predicate method AlgorithmSuiteInfo?(a: AlgorithmSuiteInfo) {
    && KeyDerivationAlgorithm?(a.kdf)
    && CommitmentDerivationAlgorithm?(a.commitment)
    && EdkWrappingAlgorithm?(a.edkWrapping)

    // If there is a KDF, the output length MUST match the encrypt length
    && (a.kdf.HKDF? ==> 
      && a.kdf.HKDF.outputKeyLength == a.encrypt.AES_GCM.keyLength)
    // If there is a signature, there MUST be a KDF
    && (a.signature.ECDSA? ==> a.kdf.HKDF?)
    // If there is commitment, the KDF MUST match
    && (a.commitment.HKDF? ==>
      && a.commitment.HKDF.saltLength == 32
      && a.commitment == a.kdf)
    // If there is a IntermediateKeyWrapping, the KDFs MUST match
    && (a.edkWrapping.IntermediateKeyWrapping? ==>
      && a.kdf.HKDF?
      && a.edkWrapping.IntermediateKeyWrapping.keyEncryptionKeyKdf == a.kdf
      && a.edkWrapping.IntermediateKeyWrapping.macKeyKdf == a.kdf)
    // If there is a KDF and no commitment then salt MUST be 0
    && (a.kdf.HKDF? && a.commitment.None? ==> a.kdf.HKDF.saltLength == 0)
    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#algorithm-suites-signature-settings
    //= type=implication
    //# An algorithm suite with a symmetric signature algorithm MUST use [intermediate key wrapping](#intermediate-key-wrapping).
    //
    // If the algorithm suite includes an symmetric signature algorithm:
    //= aws-encryption-sdk-specification/framework/algorithm-suites.md#symmetric-signature-algorithm
    //# - The algorithm suite MUST also use [Intermediate Key Wrapping](#intermediate-key-wrapping).
    && (!a.symmetricSignature.None? ==>
      && a.edkWrapping.IntermediateKeyWrapping?)
  }

  // These are the specific Algorithm Suites definitions for the ESDK.
  // Because the Smithy side can not fully express these kinds of requirements
  // it only has the `AlgorithmSuiteId`.
  // This means that on the cryptographic materials
  // there is only a `AlgorithmSuiteId`.
  // For Dafny to be able to reason practically about the `AlgorithmSuite`
  // it needs to be able to prove that
  // GetSuite(suite.id) == suite
  predicate method ESDKAlgorithmSuite?(a: AlgorithmSuiteInfo)
    requires a.id.ESDK?
  {
    // Adheres to constraints for all algorithm suites
    && AlgorithmSuiteInfo?(a)
    // All ESDK encrypt with AES_GCM
    && SupportedESDKEncrypt?(a.encrypt)

    // Specification for each supported ESDK Algorithm Suite
    && match a.id.ESDK
      // Legacy non-KDF suites

      case ALG_AES_128_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 16
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_192_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 24
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_256_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?

      // HKDF suites

      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?

      // Signature suites

      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256() =>
        && a.binaryId == [0x02, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P256
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384() =>
        && a.binaryId == [0x03, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_384
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384() =>
        && a.binaryId == [0x03, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_384
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.None?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?

      // Suites with key commitment

      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY() =>
        && a.binaryId == [0x04, 0x78]
        && a.messageVersion == 2
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.None?
        && a.commitment.HKDF?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384() =>
        && a.binaryId == [0x05, 0x78]
        && a.messageVersion == 2
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.HKDF?
        && a.symmetricSignature.None?
        && a.edkWrapping.DIRECT_KEY_WRAPPING?
  }

  predicate method DBEAlgorithmSuite?(a: AlgorithmSuiteInfo)
    requires a.id.DBE?
  {
    // Adheres to general Algorithm Suite constraints
    && AlgorithmSuiteInfo?(a)

    // DBE only supports suites with AES_GCM 256
    && SupportedDBEEncrypt?(a.encrypt)

    // DBE only supports suites with intermediate provider wrapping keys
    && SupportedDBEEDKWrapping?(a.edkWrapping)

    // Specification for each supported DBE Algorithm Suite
    && match a.id.DBE
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384() =>
        && a.binaryId == [0x67, 0x00]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.None?
        && a.commitment.HKDF?
        && a.symmetricSignature.HMAC?
        && a.symmetricSignature.HMAC == AwsCryptographyPrimitivesTypes.SHA_384
        && a.edkWrapping.IntermediateKeyWrapping?
        && a.edkWrapping.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM?
        && a.edkWrapping.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.keyLength == 32
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384() =>
        && a.binaryId == [0x67, 0x01]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.HKDF?
        && a.symmetricSignature.HMAC?
        && a.symmetricSignature.HMAC == AwsCryptographyPrimitivesTypes.SHA_384
        && a.edkWrapping.IntermediateKeyWrapping?
        && a.edkWrapping.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM?
        && a.edkWrapping.IntermediateKeyWrapping.pdkEncryptAlgorithm.AES_GCM.keyLength == 32
  }

  predicate method AlgorithmSuite?(a: AlgorithmSuiteInfo) {
    match a.id
      case ESDK(_) => ESDKAlgorithmSuite?(a)
      case DBE(_) => DBEAlgorithmSuite?(a)
  }

  type AlgorithmSuite = a: AlgorithmSuiteInfo | AlgorithmSuite?(a)
  witness *

  const Bits256 := 32 as int32;
  const Bits192 := 24 as int32;
  const Bits128 := 16 as int32;
  const TagLen := 16 as int32;
  const IvLen := 12 as int32;

  const AES_128_GCM_IV12_TAG16 := Encrypt.AES_GCM(AwsCryptographyPrimitivesTypes.AES_GCM(
    keyLength := Bits128,
    tagLength := TagLen,
    ivLength := IvLen
  ));
  const AES_192_GCM_IV12_TAG16 := Encrypt.AES_GCM(AwsCryptographyPrimitivesTypes.AES_GCM(
    keyLength := Bits192,
    tagLength := TagLen,
    ivLength := IvLen
  ));
  const AES_256_GCM_IV12_TAG16 := Encrypt.AES_GCM(AwsCryptographyPrimitivesTypes.AES_GCM(
    keyLength := Bits256,
    tagLength := TagLen,
    ivLength := IvLen
  ));

  function method HKDF_SHA_256(
    keyLength: AwsCryptographyPrimitivesTypes.SymmetricKeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(HKDF.HKDF(
      hmac := AwsCryptographyPrimitivesTypes.SHA_256,
      saltLength := 0 as int32,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    ))
  }

  function method HKDF_SHA_384(
    keyLength: AwsCryptographyPrimitivesTypes.SymmetricKeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(HKDF.HKDF(
      hmac := AwsCryptographyPrimitivesTypes.SHA_384,
      saltLength := 0 as int32,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    ))
  }

  function method HKDF_SHA_512(
    keyLength: AwsCryptographyPrimitivesTypes.SymmetricKeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(HKDF.HKDF(
      hmac := AwsCryptographyPrimitivesTypes.SHA_512,
      saltLength := 32 as int32,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    ))
  }

  const EDK_INTERMEDIATE_WRAPPING_AES_GCM_256_HKDF_SHA_512 := EdkWrappingAlgorithm.IntermediateKeyWrapping(
    IntermediateKeyWrapping.IntermediateKeyWrapping(
      keyEncryptionKeyKdf := HKDF_SHA_512(Bits256),
      macKeyKdf := HKDF_SHA_512(Bits256),
      pdkEncryptAlgorithm := AES_256_GCM_IV12_TAG16
    )
  )

  // DBE algorithm suites

  const DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.DBE(DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384),
    binaryId := [0x67, 0x00],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.HMAC(AwsCryptographyPrimitivesTypes.SHA_384),
    edkWrapping := EDK_INTERMEDIATE_WRAPPING_AES_GCM_256_HKDF_SHA_512
  )
  const DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.DBE(DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384),
    binaryId := [0x67, 0x01],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384)),
    symmetricSignature := SymmetricSignatureAlgorithm.HMAC(AwsCryptographyPrimitivesTypes.SHA_384),
    edkWrapping := EDK_INTERMEDIATE_WRAPPING_AES_GCM_256_HKDF_SHA_512
  )

  // ESDK algorithm suites

  // Non-KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x46],
    messageVersion := 1,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )

  //Non-Signature KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x46],
    messageVersion := 1,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits192),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits256),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )

  //Signature KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256),
    binaryId := [0x02, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P256)),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    encrypt := AES_192_GCM_IV12_TAG16,
    binaryId := [0x03, 0x46],
    messageVersion := 1,
    kdf := HKDF_SHA_384(Bits192),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384)),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    binaryId := [0x03, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_384(Bits256),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384)),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )

  // Commitment Suites
  const ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY),
    binaryId := [0x04, 0x78],
    messageVersion := 2,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.None(None.None),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )
  const ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384),
    binaryId := [0x05, 0x78],
    messageVersion := 2,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384)),
    symmetricSignature := SymmetricSignatureAlgorithm.None(None.None),
    edkWrapping := EdkWrappingAlgorithm.DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING.DIRECT_KEY_WRAPPING)
  )

  function method GetSuite(
    id: AlgorithmSuiteId
  ):
    (res: AlgorithmSuite)
    ensures res.id == id
  {
    match id
      case ESDK(e) => GetESDKSuite(e)
      case DBE(e) => GetDBESuite(e)
  }

  lemma LemmaAlgorithmSuiteIdImpliesEquality(id: AlgorithmSuiteId, suite: AlgorithmSuite)
    requires id == suite.id
    ensures GetSuite(id) == suite
  {
    match id
      case ESDK(e) => {
        LemmaESDKAlgorithmSuiteIdImpliesEquality(e, suite);
      }
      case DBE(e) => {
        LemmaDBEAlgorithmSuiteIdImpliesEquality(e, suite);
      }
  }

  lemma LemmaBinaryIdIsUnique(a: AlgorithmSuite, b: AlgorithmSuite)
    requires a.id != b.id
    ensures a.binaryId != b.binaryId
  {}

  /////////////////////////// DBE Suites ///////////////////////////////

  const SupportedDBEAlgorithmSuites: map<DBEAlgorithmSuiteId, AlgorithmSuite> := map[
    DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384 := DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384,
    DBEAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384 := DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384
  ];

  lemma LemmaSupportedDBEAlgorithmSuitesIsComplete(id: DBEAlgorithmSuiteId)
    ensures id in SupportedDBEAlgorithmSuites
  {}

  function method GetDBESuite(
    id: DBEAlgorithmSuiteId
  ):
    (res: AlgorithmSuite)
    ensures
    && res.id.DBE?
    && res.id.DBE == id
  {
    LemmaSupportedDBEAlgorithmSuitesIsComplete(id);
    SupportedDBEAlgorithmSuites[id]
  }

  lemma LemmaDBEAlgorithmSuiteIdImpliesEquality(id: DBEAlgorithmSuiteId, suite: AlgorithmSuite)
    requires 
    && suite.id.DBE?
    && id == suite.id.DBE
    ensures GetDBESuite(id) == suite
  {
    if GetDBESuite(id) != suite {}
  }

  /////////////////////////// ESDK Suites ///////////////////////////////


  const SupportedESDKAlgorithmSuites: map<ESDKAlgorithmSuiteId, AlgorithmSuite> := map[
    ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF := ESDK_ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF := ESDK_ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF := ESDK_ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 := ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 := ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 := ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY := ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 := ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
  ];

  lemma LemmaSupportedESDKAlgorithmSuitesIsComplete(id: ESDKAlgorithmSuiteId)
    ensures id in SupportedESDKAlgorithmSuites
  {}

  function method GetESDKSuite(
    id: ESDKAlgorithmSuiteId
  ):
    (res: AlgorithmSuite)
    ensures
    && res.id.ESDK?
    && res.id.ESDK == id
  {
    LemmaSupportedESDKAlgorithmSuitesIsComplete(id);
    SupportedESDKAlgorithmSuites[id]
  }

  lemma LemmaESDKAlgorithmSuiteIdImpliesEquality(id: ESDKAlgorithmSuiteId, suite: AlgorithmSuite)
    requires 
    && suite.id.ESDK?
    && id == suite.id.ESDK
    ensures GetESDKSuite(id) == suite
  {
    if GetESDKSuite(id) != suite {
      assert GetESDKSuite(id).encrypt.AES_GCM.tagLength == suite.encrypt.AES_GCM.tagLength;
    }
  }

  function method GetEncryptKeyLength(a: AlgorithmSuiteInfo)
    : (output: int32)
    ensures
      && AwsCryptographyPrimitivesTypes.IsValid_PositiveInteger(output)
      && AwsCryptographyPrimitivesTypes.IsValid_SymmetricKeyLength(output)
    ensures a.encrypt.AES_GCM? ==> output == a.encrypt.AES_GCM.keyLength
  {
    match a.encrypt
      case AES_GCM(e) => e.keyLength
  }

  function method GetEncryptTagLength(a: AlgorithmSuiteInfo)
    : (output: int32)
    ensures
      && AwsCryptographyPrimitivesTypes.IsValid_PositiveInteger(output)
      && AwsCryptographyPrimitivesTypes.IsValid_Uint8Bytes(output)
    ensures a.encrypt.AES_GCM? ==> output == a.encrypt.AES_GCM.tagLength
  {
    match a.encrypt
      case AES_GCM(e) => e.tagLength
  }

  function method GetEncryptIvLength(a: AlgorithmSuiteInfo)
    : (output: int32)
    ensures
      && AwsCryptographyPrimitivesTypes.IsValid_PositiveInteger(output)
      && AwsCryptographyPrimitivesTypes.IsValid_Uint8Bits(output)
    ensures a.encrypt.AES_GCM? ==> output == a.encrypt.AES_GCM.ivLength
  {
    match a.encrypt
      case AES_GCM(e) => e.ivLength
  }

  const AlgorithmSuiteInfoByBinaryId: map<seq<uint8>, AlgorithmSuite> := map[
    [0x00, 0x14] := ESDK_ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    [0x00, 0x46] := ESDK_ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    [0x00, 0x78] := ESDK_ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    [0x01, 0x14] := ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    [0x01, 0x46] := ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    [0x01, 0x78] := ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    [0x02, 0x14] := ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    [0x03, 0x46] := ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    [0x03, 0x78] := ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    [0x04, 0x78] := ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    [0x05, 0x78] := ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
    [0x67, 0x00] := DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384,
    [0x67, 0x01] := DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384
  ];

  lemma AlgorithmSuiteInfoByBinaryIdIsComplete(a: AlgorithmSuite)
    ensures a == AlgorithmSuiteInfoByBinaryId[a.binaryId]
  {}

  function method GetAlgorithmSuiteInfo(binaryId?: seq<uint8>)
    : (output: Wrappers.Result<AlgorithmSuiteInfo, Error>)
  {
    :- Wrappers.Need(binaryId? in AlgorithmSuiteInfoByBinaryId, 
      AwsCryptographicMaterialProvidersException(
        message := "Invalid BinaryId")
    );

    Wrappers.Success(AlgorithmSuiteInfoByBinaryId[binaryId?])
  }

  //= aws-encryption-sdk-specification/framework/algorithm-suites.md#supported-algorithm-suites
  //= type=implication
  //# The value `00 00` is reserved
  //# and MUST NOT be used
  //# as an Algorithm Suite ID in the future.
  lemma ReservedAlgorithmSuiteId(a: AlgorithmSuite)
    ensures a.binaryId != [0x00, 0x00]
  {}

  //= aws-encryption-sdk-specification/framework/algorithm-suites.md#supported-algorithm-suites
  //= type=implication
  //# Algorithm Suite ID MUST be a unique hex value across all supported algorithm suites.
  //
  //= aws-encryption-sdk-specification/framework/algorithm-suites.md#algorithm-suite-id
  //= type=implication
  //# A 2-byte hex value that MUST uniquely identify an algorithm suite.
  lemma AlgorithmSuiteIdIsUnique(a: AlgorithmSuite, b: AlgorithmSuite)
    requires a.id != b.id
    ensures a.binaryId != b.binaryId
  {}

}
