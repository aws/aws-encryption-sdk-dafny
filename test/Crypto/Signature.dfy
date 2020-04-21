include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"
include "../../src/Util/UTF8.dfy"

module TestSignature {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Signature
    
  module Helpers {
    import Signature
    import UTF8
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    method RequireGoodKeyLengths(s: Signature.ECDSAParams, sigKeyPair: Signature.SignatureKeyPair) {
      // The following is a declared postcondition of the KeyGen method:
      expect |sigKeyPair.verificationKey| == s.FieldSize();
    }

    method YCompression(s: Signature.ECDSAParams, fieldSize: nat) {
      var res :- expect Signature.KeyGen(s);
      RequireGoodKeyLengths(s, res);
      var public, secret := res.verificationKey, res.signingKey;
      // This is the declared postcondition of the natively implemented KenGen method, plus a condition
      // about zero-padding:
      expect 0 < |secret|;
      expect |public| == 1 + (fieldSize + 7) / 8;  // 1 byte for y; x zero-padded up to the field size
      expect public[0] == 2 || public[0] == 3;  // public key uses y compression
    }

    method VerifyMessage(params: Signature.ECDSAParams) {
      var message :- expect UTF8.Encode("Hello, World!");
      var keys :- expect Signature.KeyGen(params);
      RequireGoodKeyLengths(params, keys);

      var digest :- expect Signature.Digest(params.DigestAlgorithm(), message);
      var signature :- expect Signature.Sign(params, keys.signingKey, digest);
      var shouldBeTrue :- expect Signature.Verify(params, keys.verificationKey, digest, signature);
      expect shouldBeTrue;

      var badDigest :- expect Signature.Digest(params.DigestAlgorithm(), message + [1]);
      var shouldBeFalse :- expect Signature.Verify(params, keys.verificationKey, badDigest, signature);
      expect !shouldBeFalse;
    }

    method ToInt(bytes: seq<uint8>) returns (n: nat) {
      n := 0;
      var i := 0;
      while i < |bytes| {
        n := 0x100 * n + bytes[i] as int;
        i := i + 1;
      }
    }

    method TestDigest(s: string, alg: Signature.DigestAlgorithm, expectedLength: nat, expected: nat)
      requires forall i :: 0 <= i < |s| && 'a' <= s[i] <= 'z'
    {
      var msg := seq(|s|, i requires 0 <= i < |s| && 'a' <= s[i] <= 'z' => s[i] as uint8);
      var digest :- expect Signature.Digest(alg, msg);
      expect |digest| == expectedLength;
      var actual := ToInt(digest);
      expect actual == expected;
    }
  }

  method {:test} YCompression384() {
    Helpers.YCompression(Signature.ECDSA_P384, 384);
  }

  method {:test} YCompression256() {
    Helpers.YCompression(Signature.ECDSA_P256, 256);
  }

  method {:test} VerifyMessage384() {
    Helpers.VerifyMessage(Signature.ECDSA_P384);
  }

  method {:test} VerifyMessage256() {
    Helpers.VerifyMessage(Signature.ECDSA_P256);
  }

  method {:test} DigestAlgorithmSelections() {
    var msg, digest;
    // Test that each of the digest algorithms is supported and that they return
    // an expected number of bytes.

    // A message length that is longer than the expected digest lengths
    msg := seq(1000, i => ('a' + (i % 26) as char) as uint8);
    digest :- expect Signature.Digest(Signature.SHA_256, msg);
    expect |digest| == 32;
    digest :- expect Signature.Digest(Signature.SHA_384, msg);
    expect |digest| == 48;
    digest :- expect Signature.Digest(Signature.SHA_512, msg);
    expect |digest| == 64;
    
    // A message length that is shorter than the expected digest lengths
    msg := seq(3, i => ('a' + (i % 26) as char) as uint8);
    digest :- expect Signature.Digest(Signature.SHA_256, msg);
    expect |digest| == 32;
    digest :- expect Signature.Digest(Signature.SHA_384, msg);
    expect |digest| == 48;
    digest :- expect Signature.Digest(Signature.SHA_512, msg);
    expect |digest| == 64;
    
    // An empty message
    msg := [];
    digest :- expect Signature.Digest(Signature.SHA_256, msg);
    expect |digest| == 32;
    digest :- expect Signature.Digest(Signature.SHA_384, msg);
    expect |digest| == 48;
    digest :- expect Signature.Digest(Signature.SHA_512, msg);
    expect |digest| == 64;
  }

  method {:test} DigestTestVectors() {
    // These test vectors are https://www.di-mgt.com.au/sha_testvectors.html.
    var s := "abc";
    Helpers.TestDigest(s, Signature.SHA_256, 32, 0x0_ba7816bf_8f01cfea_414140de_5dae2223_b00361a3_96177a9c_b410ff61_f20015ad);
    Helpers.TestDigest(s, Signature.SHA_384, 48, 0x0_cb00753f45a35e8b_b5a03d699ac65007_272c32ab0eded163_1a8b605a43ff5bed_8086072ba1e7cc23_58baeca134c825a7);
    Helpers.TestDigest(s, Signature.SHA_512, 64, 0x0_ddaf35a193617aba_cc417349ae204131_12e6fa4e89a97ea2_0a9eeee64b55d39a_2192992a274fc1a8_36ba3c23a3feebbd_454d4423643ce80e_2a9ac94fa54ca49f);
    
    s := "";
    Helpers.TestDigest(s, Signature.SHA_256, 32, 0x0_e3b0c442_98fc1c14_9afbf4c8_996fb924_27ae41e4_649b934c_a495991b_7852b855);
    Helpers.TestDigest(s, Signature.SHA_384, 48, 0x0_38b060a751ac9638_4cd9327eb1b1e36a_21fdb71114be0743_4c0cc7bf63f6e1da_274edebfe76f65fb_d51ad2f14898b95b);
    Helpers.TestDigest(s, Signature.SHA_512, 64, 0x0_cf83e1357eefb8bd_f1542850d66d8007_d620e4050b5715dc_83f4a921d36ce9ce_47d0d13c5d85f2b0_ff8318d2877eec2f_63b931bd47417a81_a538327af927da3e);
    
    s := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    Helpers.TestDigest(s, Signature.SHA_256, 32, 0x0_cf5b16a7_78af8380_036ce59e_7b049237_0b249b11_e8f07a51_afac4503_7afee9d1);
    Helpers.TestDigest(s, Signature.SHA_384, 48, 0x0_09330c33f71147e8_3d192fc782cd1b47_53111b173b3b05d2_2fa08086e3b0f712_fcc7c71a557e2db9_66c3e9fa91746039);
    Helpers.TestDigest(s, Signature.SHA_512, 64, 0x0_8e959b75dae313da_8cf4f72814fc143f_8f7779c6eb9f7fa1_7299aeadb6889018_501d289e4900f7e4_331b99dec4b5433a_c7d329eeb6dd2654_5e96e55b874be909);
  }
}
