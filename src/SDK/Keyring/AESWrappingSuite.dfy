include "../../Crypto/AESUtils.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Crypto/GenBytes.dfy"

module AESKeyring.AESWrappingSuite {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AES = AESUtils
  import RNG

  const VALID_ALGORITHMS := {AES.AES_GCM_128, AES.AES_GCM_192, AES.AES_GCM_256}

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
