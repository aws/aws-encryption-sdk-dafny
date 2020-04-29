include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Digest.dfy"

module TestDigest {
  import Digest

  module Helpers {
    import Digest
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    method ToInt(bytes: seq<uint8>) returns (n: nat) {
      n := 0;
      var i := 0;
      while i < |bytes| {
        n := 0x100 * n + bytes[i] as int;
        i := i + 1;
      }
    }

    method TestDigest(s: string, alg: Digest.Algorithm, expectedLength: nat, expected: nat)
    {
      expect forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z';
      var msg := seq(|s|, i requires 0 <= i < |s| && 'a' <= s[i] <= 'z' => s[i] as uint8);
      var digest :- expect Digest.Digest(alg, msg);
      expect |digest| == expectedLength;
      var actual := ToInt(digest);
      expect actual == expected;
    }
  }

  method {:test} DigestTestVectors() {
    // These test vectors are https://www.di-mgt.com.au/sha_testvectors.html.
    var s := "abc";
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_ddaf35a193617aba_cc417349ae204131_12e6fa4e89a97ea2_0a9eeee64b55d39a_2192992a274fc1a8_36ba3c23a3feebbd_454d4423643ce80e_2a9ac94fa54ca49f);

    s := "";
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_cf83e1357eefb8bd_f1542850d66d8007_d620e4050b5715dc_83f4a921d36ce9ce_47d0d13c5d85f2b0_ff8318d2877eec2f_63b931bd47417a81_a538327af927da3e);

    s := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_8e959b75dae313da_8cf4f72814fc143f_8f7779c6eb9f7fa1_7299aeadb6889018_501d289e4900f7e4_331b99dec4b5433a_c7d329eeb6dd2654_5e96e55b874be909);
  }
}
