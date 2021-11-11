// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module 
  {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient2.AlgorithmSuites"}
  AwsCryptographicMaterialProviders2.AlgorithmSuites
{
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Aws.Crypto

  type KeyLength = l: uint8 | l == 32 || l == 24 || l == 16 witness 32
  type TagLength = l: uint8 | l == 16 witness 16
  type IVLength = l: uint8 | l == 12 witness 12

  datatype EncryptionAlgorithm = AES(mode: AESMode)
  datatype AESMode = GCM
  datatype KeyDerivationAlgorithm_ =
    | HKDF_WITH_SHA_512(inputKeyLength:KeyLength, saltLength: KeyLength)
    | HKDF_WITH_SHA_384(inputKeyLength:KeyLength)
    | HKDF_WITH_SHA_256(inputKeyLength:KeyLength)
    | IDENTITY

  type KeyDerivationAlgorithm = kdf: KeyDerivationAlgorithm_
    | kdf.HKDF_WITH_SHA_512? ==> kdf.inputKeyLength == 32
    witness *

  datatype CommitmentDerivationAlgorithm =
    | Algorithm(kdf: KeyDerivationAlgorithm)
    | None

  type HKDFAlgorithms = kdf: KeyDerivationAlgorithm | !kdf.IDENTITY? witness *
  type IdentityAlgorithm = kdf: KeyDerivationAlgorithm | kdf.IDENTITY? witness *

  datatype SignatureAlgorithm =
    | ECDSA_P_384_SHA_384
    | ECDSA_P_256_SHA_256
    | None

  datatype AlgorithmSuite_ = AlgorithmSuite_(
    nameonly id: Crypto.AlgorithmSuiteId,
    nameonly alg: EncryptionAlgorithm,
    nameonly keyLen: KeyLength,
    nameonly tagLen: TagLength,
    nameonly ivLen: IVLength,
    nameonly kdf: KeyDerivationAlgorithm,
    nameonly commitment: CommitmentDerivationAlgorithm,
    nameonly signature: SignatureAlgorithm
  )

  type AlgorithmSuite = a: AlgorithmSuite_ |
    && (!a.kdf.IDENTITY? ==> a.kdf.inputKeyLength == a.keyLen)
    && (a.commitment.Algorithm?
      ==>
        && a.keyLen == 32
        && a.kdf.HKDF_WITH_SHA_512?
        && a.kdf.saltLength == 32
        && a.commitment.kdf == a.kdf)

  witness *

  const Bits256 := 32 as KeyLength;
  const Bits192 := 24 as KeyLength;
  const Bits128 := 16 as KeyLength;
  const TagLen := 16 as TagLength;
  const IvLen := 12 as IVLength;


  // All algorithum suites

  // Non-KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    alg := AES(GCM),
    keyLen := Bits128,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    alg := AES(GCM),
    keyLen := Bits192,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    alg := AES(GCM),
    keyLen := Bits256,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Non-Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    alg := AES(GCM),
    keyLen := Bits128,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_256(Bits128),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    alg := AES(GCM),
    keyLen := Bits192,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_256(Bits192),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    alg := AES(GCM),
    keyLen := Bits256,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_256(Bits256),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    alg := AES(GCM),
    keyLen := Bits128,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_256(Bits128),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA_P_256_SHA_256
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    alg := AES(GCM),
    keyLen := Bits192,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_384(Bits192),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA_P_384_SHA_384
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    alg := AES(GCM),
    keyLen := Bits256,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_384(Bits256),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA_P_384_SHA_384
  )

  // Commitment Suites
    const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    alg := AES(GCM),
    keyLen := Bits256,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_512(Bits256, Bits256),
    commitment := CommitmentDerivationAlgorithm.Algorithm(KeyDerivationAlgorithm_.HKDF_WITH_SHA_512(Bits256, Bits256)),
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: AlgorithmSuite := AlgorithmSuite_(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
    alg := AES(GCM),
    keyLen := Bits256,
    tagLen := TagLen,
    ivLen := IvLen,
    kdf := KeyDerivationAlgorithm_.HKDF_WITH_SHA_512(Bits256, Bits256),
    commitment := CommitmentDerivationAlgorithm.Algorithm(KeyDerivationAlgorithm_.HKDF_WITH_SHA_512(Bits256, Bits256)),
    signature := SignatureAlgorithm.ECDSA_P_384_SHA_384
  )

  const SupportedAlgorithmSuites: map<Crypto.AlgorithmSuiteId, AlgorithmSuite> := map[
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF := ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF := ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF := ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 := ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 := ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 := ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY := ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 := ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
  ];

  function method GetSuite(id: Crypto.AlgorithmSuiteId): AlgorithmSuite {
    SupportedAlgorithmSuites[id]
  }
}
