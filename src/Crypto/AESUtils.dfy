include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "AESUtils"} AESUtils {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype Params = Params(keyLen: uint8, tagLen: uint8, ivLen: uint8)

  const MAX_KEY_LEN := 32
  const CIPHER_KEY_LENGTHS := {32, 24, 16};
  const TAG_LEN := 16 as uint8;
  const IV_LEN := 12 as uint8;

  const AES_GCM_128 := Params(16, TAG_LEN, IV_LEN)
  const AES_GCM_192 := Params(24, TAG_LEN, IV_LEN)
  const AES_GCM_256 := Params(32, TAG_LEN, IV_LEN)
}
