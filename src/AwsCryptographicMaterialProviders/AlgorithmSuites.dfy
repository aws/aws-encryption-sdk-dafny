// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../libraries/src/Collections/Maps/Maps.dfy"
include "../Crypto/HKDF/HMAC.dfy"
include "../Crypto/Signature.dfy"
include "../Crypto/AESEncryption.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.AlgorithmSuites"}
  MaterialProviders.AlgorithmSuites
{
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Maps
  import Aws.Crypto
  import HMAC
  import Signature
  import AESEncryption

  export
    provides
      Wrappers,
      HMAC,
      AESEncryption,
      Signature,
      Crypto,
      GetSuite
    reveals
      DerivationAlgorithm,
      KeyDerivationAlgorithm,
      CommitmentDerivationAlgorithm,
      SignatureAlgorithm,
      AlgorithmSuiteInfo,
      AlgorithmSuite,
      AlgorithmSuiteInfo

  datatype DerivationAlgorithm =
    | HKDF(
      nameonly hmac: HMAC.Digests,
      nameonly saltLength: int,
      nameonly inputKeyLength: AESEncryption.KeyLength,
      nameonly outputKeyLength: AESEncryption.KeyLength
    )
    // We are using both `IDENTITY` and `None` here
    // to modle the fact that deriving
    // the data encryption key and the commitment key
    // MUST be the same.
    // The specification treats NO_KDF as an identity operation.
    // So this naming convention mirrors the specification.
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
        && (a.signature.curve.ECDSA_P256? ==>
          && a.encrypt.keyLength == 16 as AESEncryption.KeyLength
          && a.kdf.hmac == HMAC.Digests.SHA_256
        )
        && (a.signature.curve.ECDSA_P384? ==>
          && (
            || a.kdf.hmac == HMAC.Digests.SHA_384
            || a.kdf.hmac == HMAC.Digests.SHA_512)
          && (
            || a.encrypt.keyLength == 24 as AESEncryption.KeyLength
            || a.encrypt.keyLength == 32 as AESEncryption.KeyLength)
        )
    )
    && (a.commitment.HKDF?
      ==>
        && a.encrypt.keyLength == 32 as AESEncryption.KeyLength
        && a.commitment.hmac.SHA_512?
        && a.commitment.saltLength == 32 as AESEncryption.KeyLength as int
        && a.commitment == a.kdf
        && (a.signature.ECDSA? ==> a.signature.curve.ECDSA_P384?))
  witness *

  const Bits256 := 32 as AESEncryption.KeyLength;
  const Bits192 := 24 as AESEncryption.KeyLength;
  const Bits128 := 16 as AESEncryption.KeyLength;
  const TagLen := 16 as AESEncryption.TagLength;
  const IvLen := 12 as AESEncryption.IVLength;

  const AES_128_GCM_IV12_TAG16 := AESEncryption.AES_GCM(
    keyLength := Bits128,
    tagLength := TagLen,
    ivLength := IvLen
  );
  const AES_192_GCM_IV12_TAG16 := AESEncryption.AES_GCM(
    keyLength := Bits192,
    tagLength := TagLen,
    ivLength := IvLen
  );
  const AES_256_GCM_IV12_TAG16 := AESEncryption.AES_GCM(
    keyLength := Bits256,
    tagLength := TagLen,
    ivLength := IvLen
  );

  function method HKDF_SHA_256(
    keyLength: AESEncryption.KeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_256,
      saltLength := 0,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    )
  }

  function method HKDF_SHA_384(
    keyLength: AESEncryption.KeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_384,
      saltLength := 0,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    )
  }

  function method HKDF_SHA_512(
    keyLength: AESEncryption.KeyLength
  ):
    (res: DerivationAlgorithm)
  {
    DerivationAlgorithm.HKDF(
      hmac := HMAC.Digests.SHA_512,
      saltLength := 32,
      inputKeyLength := keyLength,
      outputKeyLength := keyLength
    )
  }

  // All algorithum suites

  // Non-KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_NO_KDF: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := KeyDerivationAlgorithm.IDENTITY,
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Non-Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits192),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits256),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.None
  )

  //Signature KDF suites
  const ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    encrypt := AES_128_GCM_IV12_TAG16,
    kdf := HKDF_SHA_256(Bits128),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P256)
  )
  const ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    encrypt := AES_192_GCM_IV12_TAG16,
    kdf := HKDF_SHA_384(Bits192),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P384)
  )
  const ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_384(Bits256),
    commitment := CommitmentDerivationAlgorithm.None,
    signature := SignatureAlgorithm.ECDSA(curve := Signature.ECDSAParams.ECDSA_P384)
  )

  // Commitment Suites
    const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
    signature := SignatureAlgorithm.None
  )
  const ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384: AlgorithmSuite := AlgorithmSuiteInfo(
    id := Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384,
    encrypt := AES_256_GCM_IV12_TAG16,
    kdf := HKDF_SHA_512(Bits256),
    commitment := HKDF_SHA_512(Bits256),
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
