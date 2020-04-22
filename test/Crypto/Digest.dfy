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
    Helpers.TestDigest(s, Digest.SHA_256, 32, 0x0_ba7816bf_8f01cfea_414140de_5dae2223_b00361a3_96177a9c_b410ff61_f20015ad);
    Helpers.TestDigest(s, Digest.SHA_384, 48, 0x0_cb00753f45a35e8b_b5a03d699ac65007_272c32ab0eded163_1a8b605a43ff5bed_8086072ba1e7cc23_58baeca134c825a7);
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_ddaf35a193617aba_cc417349ae204131_12e6fa4e89a97ea2_0a9eeee64b55d39a_2192992a274fc1a8_36ba3c23a3feebbd_454d4423643ce80e_2a9ac94fa54ca49f);
    
    s := "";
    Helpers.TestDigest(s, Digest.SHA_256, 32, 0x0_e3b0c442_98fc1c14_9afbf4c8_996fb924_27ae41e4_649b934c_a495991b_7852b855);
    Helpers.TestDigest(s, Digest.SHA_384, 48, 0x0_38b060a751ac9638_4cd9327eb1b1e36a_21fdb71114be0743_4c0cc7bf63f6e1da_274edebfe76f65fb_d51ad2f14898b95b);
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_cf83e1357eefb8bd_f1542850d66d8007_d620e4050b5715dc_83f4a921d36ce9ce_47d0d13c5d85f2b0_ff8318d2877eec2f_63b931bd47417a81_a538327af927da3e);
    
    s := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    Helpers.TestDigest(s, Digest.SHA_256, 32, 0x0_cf5b16a7_78af8380_036ce59e_7b049237_0b249b11_e8f07a51_afac4503_7afee9d1);
    Helpers.TestDigest(s, Digest.SHA_384, 48, 0x0_09330c33f71147e8_3d192fc782cd1b47_53111b173b3b05d2_2fa08086e3b0f712_fcc7c71a557e2db9_66c3e9fa91746039);
    Helpers.TestDigest(s, Digest.SHA_512, 64, 0x0_8e959b75dae313da_8cf4f72814fc143f_8f7779c6eb9f7fa1_7299aeadb6889018_501d289e4900f7e4_331b99dec4b5433a_c7d329eeb6dd2654_5e96e55b874be909);
  }
}
