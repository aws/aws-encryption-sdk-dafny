include "../Crypto/All.dfy"
include "../Crypto/Cipher.dfy"
include "../Crypto/Digests.dfy"
include "../Util/StandardLibrary.dfy"

module AlgorithmSuite {

  import opened Cipher
  import Digests
  import S = Signature
  import opened StandardLibrary

  newtype ID = x | 0 <= x < 0x1_0000
  const AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384 : ID := 0x0378
  const AES_192_GCM_IV12_AUTH16_KDSHA384_SIGEC384 : ID := 0x0346
  const AES_128_GCM_IV12_AUTH16_KDSHA256_SIGEC256 : ID := 0x0214
  const AES_256_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : ID := 0x0178
  const AES_192_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : ID := 0x0146
  const AES_128_GCM_IV12_AUTH16_KDSHA256_SIGNONE  : ID := 0x0114
  const AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE    : ID := 0x0078
  const AES_192_GCM_IV12_AUTH16_KDNONE_SIGNONE    : ID := 0x0046
  const AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE    : ID := 0x0014

  datatype AlgSuite = AlgSuite(params : Cipher.CipherParams, hkdf : Digests.HMAC_ALGORITHM, sign : Option<S.ECDSAParams>)

  const Suite := map [
    AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384 := AlgSuite(CipherParams(AES256, 16, 12), Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_192_GCM_IV12_AUTH16_KDSHA384_SIGEC384 := AlgSuite(CipherParams(AES192, 16, 12), Digests.HmacSHA384, Some(S.ECDSA_P384)),
    AES_128_GCM_IV12_AUTH16_KDSHA256_SIGEC256 := AlgSuite(CipherParams(AES128, 16, 12), Digests.HmacSHA256, Some(S.ECDSA_P256)),
    AES_256_GCM_IV12_AUTH16_KDSHA256_SIGNONE  := AlgSuite(CipherParams(AES256, 16, 12), Digests.HmacSHA256, None),
    AES_192_GCM_IV12_AUTH16_KDSHA256_SIGNONE  := AlgSuite(CipherParams(AES192, 16, 12), Digests.HmacSHA256, None),
    AES_128_GCM_IV12_AUTH16_KDSHA256_SIGNONE  := AlgSuite(CipherParams(AES128, 16, 12), Digests.HmacSHA256, None),
    AES_256_GCM_IV12_AUTH16_KDNONE_SIGNONE    := AlgSuite(CipherParams(AES256, 16, 12), Digests.HmacNOSHA,  None),
    AES_192_GCM_IV12_AUTH16_KDNONE_SIGNONE    := AlgSuite(CipherParams(AES192, 16, 12), Digests.HmacNOSHA,  None),
    AES_128_GCM_IV12_AUTH16_KDNONE_SIGNONE    := AlgSuite(CipherParams(AES128, 16, 12), Digests.HmacNOSHA,  None)
  ]

}