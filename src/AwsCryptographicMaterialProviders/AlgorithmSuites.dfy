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
      GetSuite,
      LemmaAlgorithmSuiteIdImpliesEquality
    reveals
      DerivationAlgorithm,
      KeyDerivationAlgorithm,
      CommitmentDerivationAlgorithm,
      SignatureAlgorithm,
      AlgorithmSuiteInfo,
      AlgorithmSuite

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
    // General constraints for all existing Algorithm Suites.
    // These are here to make sure that these are true.

    // If there is a KDF, the output length MUST match the encrypt length
    && (a.kdf.HKDF? ==> a.kdf.outputKeyLength == a.encrypt.keyLength)
    // If there is a signature, there MUST be a KDF
    && (a.signature.ECDSA? ==> a.kdf.HKDF?)
    // If there is commitment, the KDF MUST match
    && (a.commitment.HKDF? ==>
      && a.commitment.saltLength == 32
      && a.commitment == a.kdf)
    // If there is a KDF and no commitment then salt MUST be 0
    && (a.kdf.HKDF? && a.commitment.None? ==> a.kdf.saltLength == 0)

    // These are the specific Algorithm Suites definitions.
    // Because the Smithy side can not fully express these kinds of requirements
    // it only has the `AlgorithmSuiteId`.
    // This means that on the cryptographic materials
    // there is only a `AlgorithmSuiteId`.
    // For Dafny to be able to reason practically about the `AlgorithmSuite`
    // it needs to be able to prove that
    // GetSuite(suite.id) == suite

    // Legacy non-KDF suites
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
      ==>
        && a.encrypt.keyLength == 16
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF
      ==>
        && a.encrypt.keyLength == 24
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF
      ==>
        && a.encrypt.keyLength == 32
        && a.kdf.IDENTITY?
        && a.signature.None?
        && a.commitment.None?)

    // HKDF suites
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256
      ==>
        && a.encrypt.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_256
        && a.signature.None?
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256
      ==>
        && a.encrypt.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_256
        && a.signature.None?
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256
      ==>
        && a.encrypt.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_256
        && a.signature.None?
        && a.commitment.None?)

    // Signature suites
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
      ==>
        && a.encrypt.keyLength == 16
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_256
        && a.signature.ECDSA?
        && a.signature.curve == Signature.ECDSAParams.ECDSA_P256
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
      ==>
        && a.encrypt.keyLength == 24
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_384
        && a.signature.ECDSA?
        && a.signature.curve == Signature.ECDSAParams.ECDSA_P384
        && a.commitment.None?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
      ==>
        && a.encrypt.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_384
        && a.signature.ECDSA?
        && a.signature.curve == Signature.ECDSAParams.ECDSA_P384
        && a.commitment.None?)

    // Suites with key commitment
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
      ==>
        && a.encrypt.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_512
        && a.signature.None?
        && a.commitment.HKDF?)
    && (a.id == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
      ==>
        && a.encrypt.keyLength == 32
        && a.kdf.HKDF?
        && a.kdf.hmac == HMAC.Digests.SHA_512
        && a.signature.ECDSA?
        && a.signature.curve == Signature.ECDSAParams.ECDSA_P384
        && a.commitment.HKDF?)
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

  // All algorithm suites

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

  function method GetSuite(
    id: Crypto.AlgorithmSuiteId
  ):
    (res: AlgorithmSuite)
  {
    LemmaSupportedAlgorithmSuitesIsComplete(id);
    SupportedAlgorithmSuites[id]
  }

  lemma LemmaAlgorithmSuiteIdImpliesEquality(id: Crypto.AlgorithmSuiteId, suite: AlgorithmSuite)
    requires id == suite.id
    ensures GetSuite(id) == suite
  {
    if GetSuite(id) != suite {
      assert GetSuite(id).encrypt.keyLength == suite.encrypt.keyLength;
    }
  }
}
