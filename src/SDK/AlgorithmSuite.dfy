include "../Crypto/EncryptionSuites.dfy"
include "../Crypto/Digests.dfy"
include "../Crypto/Signature.dfy"
include "../StandardLibrary/StandardLibrary.dfy"

module AlgorithmSuite {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionSuites
  import S = Signature
  import Digests

  const VALID_IDS: set<uint16> := {0x0378, 0x0346, 0x0214, 0x0178, 0x0146, 0x0114, 0x0078, 0x0046, 0x0014};

  newtype ID = x | x in VALID_IDS witness 0x0014
  {
    function method Algorithm(): EncryptionSuites.EncryptionSuite
      ensures Algorithm().Valid()
    {
      Suite[this].algorithm
    }

    function method KeyLength(): nat {
      Suite[this].algorithm.keyLen as nat
    }

    function method KDFInputKeyLength(): nat
      ensures Suite[this].hkdf == Digests.HmacNOSHA ==> KDFInputKeyLength() == KeyLength()
    {
      KeyLength()
    }

    function method IVLength(): nat {
      Suite[this].algorithm.ivLen as nat
    }

    function method TagLength(): nat {
      Suite[this].algorithm.tagLen as nat
    }

    function method SignatureType(): Option<S.ECDSAParams> {
      Suite[this].sign
    }
  }

  const AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 0x0378
  const AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 0x0346
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: ID := 0x0214
  const AES_256_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE:    ID := 0x0178
  const AES_192_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE:    ID := 0x0146
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE:    ID := 0x0114
  const AES_256_GCM_IV12_TAG16_KDFNONE_SIGNONE:        ID := 0x0078
  const AES_192_GCM_IV12_TAG16_KDFNONE_SIGNONE:        ID := 0x0046
  const AES_128_GCM_IV12_TAG16_KDFNONE_SIGNONE:        ID := 0x0014

  datatype AlgSuite = AlgSuite(algorithm: EncryptionSuites.EncryptionSuite, hkdf: Digests.HMAC_ALGORITHM, sign: Option<S.ECDSAParams>)

  const Suite := map [
    AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacSHA256, Some(S.ECDSA_P256)),
    AES_256_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacSHA256, None),
    AES_192_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacSHA256, None),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacSHA256, None),
    AES_256_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacNOSHA,  None),
    AES_192_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacNOSHA,  None),
    AES_128_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacNOSHA,  None)
  ]

  /* Suite is intended to have an entry for each possible value of ID. This is stated and checked in three ways.
   *   - lemma SuiteIsCompletes states and proves the connection between type ID and Suite.Keys
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
}
