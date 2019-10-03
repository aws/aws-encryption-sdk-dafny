include "../Crypto/AESUtils.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "GenBytes.dfy"

module WrappingAlgorithmSuite {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AES = AESUtils
  import RNG

  const AES_GCM_128 := AES.Params(AES.AES128, AES.KeyLengthOfCipher(AES.AES128), AES.TAG_LEN, AES.IV_LEN)
  const AES_GCM_192 := AES.Params(AES.AES192, AES.KeyLengthOfCipher(AES.AES192), AES.TAG_LEN, AES.IV_LEN)
  const AES_GCM_256 := AES.Params(AES.AES256, AES.KeyLengthOfCipher(AES.AES256), AES.TAG_LEN, AES.IV_LEN)

  const VALID_ALGORITHMS := {AES_GCM_128, AES_GCM_192, AES_GCM_256}

  method GenIV(p: AES.Params) returns (s: seq<uint8>)
    ensures |s| == p.ivLen as int
  {
    s := RNG.GenBytes(p.ivLen as uint16);
  }

  method GenKey(p: AES.Params) returns (s: seq<uint8>)
    ensures |s| == p.keyLen as int
  {
    s := RNG.GenBytes(p.keyLen as uint16);
  }
}
