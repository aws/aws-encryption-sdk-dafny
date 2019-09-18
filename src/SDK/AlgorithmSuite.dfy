//include "../Crypto/All.dfy"
include "../Crypto/Cipher.dfy"
include "../Crypto/Digests.dfy"
include "../Crypto/Signature.dfy"
include "../StandardLibrary/StandardLibrary.dfy"

module AlgorithmSuite {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import S = Signature
  import C = Cipher
  import Digests

  const validIDs: set<uint16> := {0x0378, 0x0346, 0x0214, 0x0178, 0x0146, 0x0114, 0x0078, 0x0046, 0x0014};

  newtype ID = x | x in validIDs witness 0x0014
  {
    function method KeyLength(): nat {
      Suite[this].params.keyLen as nat
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

  datatype AlgSuite = AlgSuite(params: C.CipherParams, hkdf: Digests.HMAC_ALGORITHM, sign: Option<S.ECDSAParams>)

  const Suite := map [
    AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(C.AES_GCM_256, Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(C.AES_GCM_192, Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := AlgSuite(C.AES_GCM_128, Digests.HmacSHA256, Some(S.ECDSA_P256)),
    AES_256_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(C.AES_GCM_256, Digests.HmacSHA256, None),
    AES_192_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(C.AES_GCM_192, Digests.HmacSHA256, None),
    AES_128_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE    := AlgSuite(C.AES_GCM_128, Digests.HmacSHA256, None),
    AES_256_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(C.AES_GCM_256, Digests.HmacNOSHA,  None),
    AES_192_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(C.AES_GCM_192, Digests.HmacNOSHA,  None),
    AES_128_GCM_IV12_TAG16_KDFNONE_SIGNONE        := AlgSuite(C.AES_GCM_128, Digests.HmacNOSHA,  None)
  ]
}
