include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "EncryptionAlgorithms"} EncryptionAlgorithms {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype Algorithm = AES(mode: AESMode)
  datatype AESMode   = GCM

  datatype Params = Params(alg: Algorithm, keyLen: uint8, tagLen: uint8, ivLen: uint8)
  {
    predicate Valid() {
      match alg
      case AES(mode) => keyLen as int in AES_CIPHER_KEY_LENGTHS && tagLen == AES_TAG_LEN && ivLen == AES_IV_LEN && mode == GCM
    }
  }

  const AES_MAX_KEY_LEN := 32
  const AES_CIPHER_KEY_LENGTHS := {32, 24, 16};
  const AES_TAG_LEN := 16 as uint8;
  const AES_IV_LEN := 12 as uint8;

  const AES_GCM_128 := Params(AES(GCM), 16, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_192 := Params(AES(GCM), 24, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_256 := Params(AES(GCM), 32, AES_TAG_LEN, AES_IV_LEN)
}
