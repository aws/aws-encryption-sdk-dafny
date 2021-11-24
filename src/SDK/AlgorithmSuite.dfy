// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Crypto/AESEncryption.dfy"
include "../Crypto/HKDF/HMAC.dfy"
include "../Crypto/Signature.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "AlgorithmSuite"} AlgorithmSuite {
  import opened Wrappers
  import Aws.Crypto
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import S = Signature
  import HMAC

  datatype KeyDerivationAlgorithms =
  | HKDF_WITH_SHA_384(digest: HMAC.Digests)
  | HKDF_WITH_SHA_256(digest: HMAC.Digests)
  | IDENTITY

  const VALID_IDS: set<uint16> := {0x0378, 0x0346, 0x0214, 0x0178, 0x0146, 0x0114, 0x0078, 0x0046, 0x0014};

  newtype ID = x | x in VALID_IDS witness 0x0014
  {
    function method EncryptionSuite(): AESEncryption.AES_GCM
    {
      Suite[this].algorithm
    }

    function method KeyLength(): nat {
      Suite[this].algorithm.keyLength as nat
    }

    predicate method ContainsIdentityKDF() {
      Suite[this].hkdf == KeyDerivationAlgorithms.IDENTITY
    }

    function method KDFInputKeyLength(): nat
      ensures ContainsIdentityKDF() ==> KDFInputKeyLength() == KeyLength()
    {
      // We're intentionally using a match here so additional Key Derivation Algorithms force us to revisit this logic
      // and we don't accidentally use Suite[this].algorithm.keyLen by default. Also, prevent or KDFInputKeyLength from
      // being tied to KeyLength().
      match Suite[this].hkdf
      case HKDF_WITH_SHA_384(_) => Suite[this].algorithm.keyLength as nat
      case HKDF_WITH_SHA_256(_) => Suite[this].algorithm.keyLength as nat
      case IDENTITY => Suite[this].algorithm.keyLength as nat
    }

    function method IVLength(): nat {
      Suite[this].algorithm.ivLength as nat
    }

    function method TagLength(): nat {
      Suite[this].algorithm.tagLength as nat
    }

    function method SignatureType(): Option<S.ECDSAParams> {
      Suite[this].sign
    }

    predicate method ValidPlaintextDataKey(plaintextDataKey: seq<uint8>) {
      |plaintextDataKey| == KDFInputKeyLength()
    }
  }

  // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/algorithms-reference.html
  const AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384:        ID := 0x0378
  const AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384:        ID := 0x0346
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256:        ID := 0x0214
  const AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG:  ID := 0x0178
  const AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG:  ID := 0x0146
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG:  ID := 0x0114
  const AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG:     ID := 0x0078
  const AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG:     ID := 0x0046
  const AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG:     ID := 0x0014

  datatype AlgSuite = AlgSuite(algorithm: AESEncryption.AES_GCM, hkdf: KeyDerivationAlgorithms, sign: Option<S.ECDSAParams>)

  const Suite := map [
    AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384       := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits256,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_384(HMAC.Digests.SHA_384),
      Some(S.ECDSA_P384)
    ),
    AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384       := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits192,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_384(HMAC.Digests.SHA_384),
      Some(S.ECDSA_P384)
    ),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256       := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits128,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_256(HMAC.Digests.SHA_256),
      Some(S.ECDSA_P256)
    ),
    AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits256,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_256(HMAC.Digests.SHA_256),
      None
    ),
    AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits192,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_256(HMAC.Digests.SHA_256),
      None
    ),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits128,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.HKDF_WITH_SHA_256(HMAC.Digests.SHA_256),
      None),
    AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG    := AlgSuite(
        AESEncryption.AES_GCM(
        keyLength := Bits256,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.IDENTITY,
      None
    ),
    AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG    := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits192,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.IDENTITY,
      None
    ),
    AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG    := AlgSuite(
      AESEncryption.AES_GCM(
        keyLength := Bits128,
        tagLength := TagLen,
        ivLength := IvLen
      ),
      KeyDerivationAlgorithms.IDENTITY,
      None
    )
  ]

  // TODO a better way to integrate the Polymorph Alg Suites with the info in this file?
  function method PolymorphIDToInternalID(input: Crypto.AlgorithmSuiteId): (res: ID) {
        if (input==Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF) then
          AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF) then
          AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF) then
          AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256) then
          AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256) then
          AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256) then
          AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
        else if (input==Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256) then
          AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
        else if (input==Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384) then
          AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
        else
          AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
  }


  function method InternalIDToPolymorphID(input: ID): (res: Crypto.AlgorithmSuiteId) {
        if (input==AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
        else if (input==AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF
        else if (input==AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF
        else if (input==AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256
        else if (input==AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256
        else if (input==AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG) then
          Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256
        else if (input==AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256) then
          Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
        else if (input==AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384) then
          Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
        else
          Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
  }

  /* Suite is intended to have an entry for each possible value of ID. This is stated and checked in three ways.
   *   - lemma SuiteIsComplete states and proves the connection between type ID and Suite.Keys
   *   - lemma ValidIDsAreSuiteKeys states and proves the connected between predicate ValidIDs and Suite.Keys
   *   - the member functions of ID use the expression `Suite[this]`, whose well-formedness relies on every
   *     ID being in Suite.Keys
   */

  lemma SuiteIsComplete(id: ID)
    ensures id in Suite.Keys
  {
  }

  lemma ValidIDsAreSuiteKeys()
    ensures VALID_IDS == set id | id in Suite.Keys :: id as uint16
  {
    forall x | x in VALID_IDS
      ensures exists id :: id in Suite.Keys && id as uint16 == x
    {
      assert x as ID in Suite.Keys;
    }
  }

  const Bits256 := 32 as AESEncryption.KeyLength;
  const Bits192 := 24 as AESEncryption.KeyLength;
  const Bits128 := 16 as AESEncryption.KeyLength;
  const TagLen := 16 as AESEncryption.TagLength;
  const IvLen := 12 as AESEncryption.IVLength;
}
