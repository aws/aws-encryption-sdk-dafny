// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AlgorithmSuites {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened AwsCryptographyMaterialProvidersTypes
  import Wrappers

  predicate method SupportedESDKEncrypt?(e: Encrypt) {
    && e.AES_GCM?
    && (
      || e.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
      || e.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 24
      || e.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 16)
    && e.AwsCryptographyPrimitivesTypesAES_GCM.tagLength == 16
    && e.AwsCryptographyPrimitivesTypesAES_GCM.ivLength == 12
  }

  predicate method KeyDerivationAlgorithm?(kdf: DerivationAlgorithm) {
    && (
        && kdf.HKDF?
      ==>
        && kdf.HKDF.inputKeyLength == kdf.HKDF.outputKeyLength
        && (kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512 ==> kdf.HKDF.inputKeyLength == 32))
    && !kdf.None?
  }

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

  // These are the specific Algorithm Suites definitions.
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
    // General constraints for all existing ESDK Algorithm Suites.
    // These are here to make sure that these are true.

    // All ESDK encrypt with AES_GCM
    && SupportedESDKEncrypt?(a.encrypt)
    && KeyDerivationAlgorithm?(a.kdf)
    && CommitmentDerivationAlgorithm?(a.commitment)

    // If there is a KDF, the output length MUST match the encrypt length
    && (a.kdf.HKDF? ==> 
      && a.kdf.HKDF.outputKeyLength == a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength)
    // If there is a signature, there MUST be a KDF
    && (a.signature.ECDSA? ==> a.kdf.HKDF?)
    // If there is commitment, the KDF MUST match
    && (a.commitment.HKDF? ==>
      && a.commitment.HKDF.saltLength == 32
      && a.commitment == a.kdf)
    // If there is a KDF and no commitment then salt MUST be 0
    && (a.kdf.HKDF? && a.commitment.None? ==> a.kdf.HKDF.saltLength == 0)
    && match a.id.ESDKAlgorithmSuiteId
      // Legacy non-KDF suites

      case ALG_AES_128_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 16
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?
      case ALG_AES_192_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 24
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?
      case ALG_AES_256_GCM_IV12_TAG16_NO_KDF() =>
        && a.binaryId == [0x00, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?

      // HKDF suites

      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256() =>
        && a.binaryId == [0x01, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.None?
        && a.commitment.None?

      // Signature suites

      case ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256() =>
        && a.binaryId == [0x02, 0x14]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_256
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P256
        && a.commitment.None?
      case ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384() =>
        && a.binaryId == [0x03, 0x46]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_384
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.None?
      case ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384() =>
        && a.binaryId == [0x03, 0x78]
        && a.messageVersion == 1
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_384
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.None?

      // Suites with key commitment

      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY() =>
        && a.binaryId == [0x04, 0x78]
        && a.messageVersion == 2
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.None?
        && a.commitment.HKDF?
      case ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384() =>
        && a.binaryId == [0x05, 0x78]
        && a.messageVersion == 2
        && a.encrypt.AES_GCM?
        && a.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.HKDF.hmac == AwsCryptographyPrimitivesTypes.SHA_512
        && a.signature.ECDSA?
        && a.signature.ECDSA.curve == AwsCryptographyPrimitivesTypes.ECDSA_P384
        && a.commitment.HKDF?
  }

  predicate method AlgorithmSuite?(a: AlgorithmSuiteInfo) {
    match a.id
      case ESDK(_) => ESDKAlgorithmSuite?(a)
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

  // All algorithm suites

  // Non-KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x46],
    messageVersion := 1,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF),
    binaryId := [0x00, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := DerivationAlgorithm.IDENTITY(IDENTITY.IDENTITY),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )

  //Non-Signature KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x46],
    messageVersion := 1,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits192),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256),
    binaryId := [0x01, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits256),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.None(None.None)
  )

  //Signature KDF suites
  const ESDK_ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256),
    binaryId := [0x02, 0x14],
    messageVersion := 1,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P256))
  )
  const ESDK_ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    encrypt := AES_192_GCM_IV12_TAG16,
    binaryId := [0x03, 0x46],
    messageVersion := 1,
    kdf := HKDF_SHA_384(Bits192),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384))
  )
  const ESDK_ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    binaryId := [0x03, 0x78],
    messageVersion := 1,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_384(Bits256),
    commitment := DerivationAlgorithm.None(None.None),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384))
  )

  // Commitment Suites
  const ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY),
    binaryId := [0x04, 0x78],
    messageVersion := 2,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.None(None.None)
  )
  const ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo.AlgorithmSuiteInfo(
    id := AlgorithmSuiteId.ESDK(ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384),
    binaryId := [0x05, 0x78],
    messageVersion := 2,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.ECDSA(ECDSA.ECDSA(curve := AwsCryptographyPrimitivesTypes.ECDSA_P384))
  )

  function method GetSuite(
    id: AlgorithmSuiteId
  ):
    (res: AlgorithmSuite)
    ensures res.id == id
  {
    match id
      case ESDK(e) => GetESDKSuite(e)
  }

  lemma LemmaAlgorithmSuiteIdImpliesEquality(id: AlgorithmSuiteId, suite: AlgorithmSuite)
    requires id == suite.id
    ensures GetSuite(id) == suite
  {
    match id
      case ESDK(e) => {
        LemmaESDKAlgorithmSuiteIdImpliesEquality(e, suite);
      }
  }

  lemma LemmaBinaryIdIsUnique(a: AlgorithmSuite, b: AlgorithmSuite)
    requires a.id != b.id
    ensures a.binaryId != b.binaryId
  {}

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
    && res.id.ESDKAlgorithmSuiteId == id
  {
    LemmaSupportedESDKAlgorithmSuitesIsComplete(id);
    SupportedESDKAlgorithmSuites[id]
  }

  lemma LemmaESDKAlgorithmSuiteIdImpliesEquality(id: ESDKAlgorithmSuiteId, suite: AlgorithmSuite)
    requires 
    && suite.id.ESDK?
    && id == suite.id.ESDKAlgorithmSuiteId
    ensures GetESDKSuite(id) == suite
  {
    if GetESDKSuite(id) != suite {
      assert GetESDKSuite(id).encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength == suite.encrypt.AwsCryptographyPrimitivesTypesAES_GCM.keyLength;
    }
  }

  function method GetEncryptKeyLength(a: AlgorithmSuiteInfo)
    : (output: int32)
    ensures
      && AwsCryptographyPrimitivesTypes.IsValid_PositiveInteger(output)
      && AwsCryptographyPrimitivesTypes.IsValid_SymmetricKeyLength(output)
  {
    match a.encrypt
      case AES_GCM(e) => e.keyLength
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
    [0x05, 0x78] := ESDK_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
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
  //# Algorithm Suite ID MUST be a unique hex value across all [supported algorithm suites](#supported-algorithm-suites).
  //
  //= aws-encryption-sdk-specification/framework/algorithm-suites.md#algorithm-suite-id
  //= type=implication
  //# A 2-byte hex value that MUST uniquely identify an algorithm suite.
  lemma AlgorithmSuiteIdIsUnique(a: AlgorithmSuite, b: AlgorithmSuite)
    requires a.id != b.id
    ensures a.binaryId != b.binaryId
  {}

}
