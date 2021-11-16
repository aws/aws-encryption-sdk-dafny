// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../libraries/src/Collections/Maps/Maps.dfy"
include "../Crypto/HKDF/HMAC.dfy"
include "../Crypto/Signature.dfy"
include "../Crypto/AESEncryption.dfy"

module 
  {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient2.AlgorithmSuites"}
  AwsCryptographicMaterialProviders2.AlgorithmSuites
{
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Maps
  import Aws.Crypto
  import HMAC
  import Signature
  import AESEncryption

  datatype DerivationAlgorithm =
    | HKDF(
      nameonly hmac: HMAC.Digests,
      nameonly saltLength: int,
      nameonly inputKeyLength: AESEncryption.KeyLength,
      nameonly outputKeyLength: AESEncryption.KeyLength
    )
    | IDENTITY
    | None

  type KeyDerivationAlgorithm = kdf: DerivationAlgorithm
    |
    && (
      && kdf.HKDF?
    ==>
      && kdf.inputKeyLength == kdf.outputKeyLength
      && (kdf.hmac == HMAC.Digests.SHA_512 ==> kdf.inputKeyLength == 32))
    && !kdf.None?
    witness *

  type CommitmentDerivationAlgorithm = kdf: DerivationAlgorithm
    |
    && (
      && kdf.HKDF?
    ==> 
      && kdf.hmac.SHA_512?
      && kdf.saltLength == 32
      && kdf.inputKeyLength == 32
      && kdf.outputKeyLength == 32)
    && !kdf.IDENTITY?

    witness *

  datatype SignatureAlgorithm =
    | ECDSA(curve: Signature.ECDSAParams)
    | None

  datatype AlgorithmSuiteInfo = AlgorithmSuiteInfo(
    nameonly id: Crypto.AlgorithmSuiteId,
    nameonly encrypt: AESEncryption.AES_GCM,
    nameonly kdf: KeyDerivationAlgorithm,
    nameonly commitment: CommitmentDerivationAlgorithm,
    nameonly signature: SignatureAlgorithm
  )

  type AlgorithmSuite = a: AlgorithmSuiteInfo |
    && (a.kdf.HKDF? ==> a.kdf.outputKeyLength == a.encrypt.keyLength)
    && (a.signature.ECDSA?
      ==> 
        && a.kdf.HKDF?
        && (a.signature.curve.ECDSA_P256? ==> a.encrypt.keyLength == Bits128)
        && (a.signature.curve.ECDSA_P384? ==>
          || a.encrypt.keyLength == Bits192
          || a.encrypt.keyLength == Bits256))
    && (a.commitment.HKDF?
      ==>
        && a.encrypt.keyLength == Bits256
        && a.commitment.hmac.SHA_512?
        && a.commitment.saltLength == Bits256 as int
        && a.commitment == a.kdf
        && (a.signature.ECDSA? ==> a.signature.curve.ECDSA_P384?))
  witness *

  const Bits256 := 32 as AESEncryption.KeyLength;
  const Bits192 := 24 as AESEncryption.KeyLength;
  const Bits128 := 16 as AESEncryption.KeyLength;
  const TagLen := 16 as AESEncryption.TagLength;
  const IvLen := 12 as AESEncryption.IVLength;

  // All algorithum suites

  // Non-KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits128,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits192,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits256,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Non-Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits128,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_256,
      saltLength := 0,
      inputKeyLength := Bits128,
      outputKeyLength := Bits128
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits192,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_256,
      saltLength := 0,
      inputKeyLength := Bits192,
      outputKeyLength := Bits192
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits256,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_256,
      saltLength := 0,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits128,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_256,
      saltLength := 0,
      inputKeyLength := Bits128,
      outputKeyLength := Bits128
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P256)
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits192,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_384,
      saltLength := 0,
      inputKeyLength := Bits192,
      outputKeyLength := Bits192
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P384)
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits256,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_384,
      saltLength := 0,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P384)
  )

  // Commitment Suites
    const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits256,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_512,
      saltLength := 32,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    commitment := CommitmentDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_512,
      saltLength := 32,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
    encrypt := AESEncryption.AES_GCM(
      keyLength := Bits256,
      tagLength := TagLen,
      ivLength := IvLen
    ),
    kdf := KeyDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_512,
      saltLength := 32,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    commitment := CommitmentDerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_512,
      saltLength := 32,
      inputKeyLength := Bits256,
      outputKeyLength := Bits256
    ),
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P384)
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

  lemma LemmaSupportedAlgorithmSuitesIsComplete(id:Crypto.AlgorithmSuiteId)
    ensures id in SupportedAlgorithmSuites
  {}

  function method GetSuite(id: Crypto.AlgorithmSuiteId): (res: AlgorithmSuite) {
    LemmaSupportedAlgorithmSuitesIsComplete(id);
    SupportedAlgorithmSuites[id]
  }
}
