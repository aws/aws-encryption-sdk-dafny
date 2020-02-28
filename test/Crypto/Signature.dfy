include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"
include "../../src/Util/UTF8.dfy"

module TestSignature {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Signature
  import UTF8

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

  method {:test} YCompression384() {
    YCompression(Signature.ECDSA_P384, 384);
  }

  method {:test} YCompression256() {
    YCompression(Signature.ECDSA_P256, 256);
  }

  method VerifyMessage(params: Signature.ECDSAParams) {
    var message :- expect UTF8.Encode("Hello, World!");
    var keys :- expect Signature.KeyGen(params);
    RequireGoodKeyLengths(params, keys);

    var digest :- expect Signature.Digest(params, message);
    var signature :- expect Signature.Sign(params, keys.signingKey, digest);
    var shouldBeTrue :- expect Signature.Verify(params, keys.verificationKey, digest, signature);
    expect shouldBeTrue;

    var badDigest :- expect Signature.Digest(params, message + [1]);
    var shouldBeFalse :- expect Signature.Verify(params, keys.verificationKey, badDigest, signature);
    expect !shouldBeFalse;
  }

  method {:test} VerifyMessage384() {
    VerifyMessage(Signature.ECDSA_P384);
  }

  method {:test} VerifyMessage256() {
    VerifyMessage(Signature.ECDSA_P256);
  }
}
