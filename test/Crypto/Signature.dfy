include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"
include "../../src/Util/UTF8.dfy"

module TestSignature {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Signature
  import UTF8

  method RequireGoodKeyLengths(s: Signature.ECDSAParams, sigKeyPair: Signature.SignatureKeyPair) returns (r: Result<()>) {
    // The following is a declared postcondition of the KeyGen method:
    var _ :- Require(|sigKeyPair.verificationKey| == s.FieldSize());
    return Success(());
  }

  method YCompression(s: Signature.ECDSAParams, fieldSize: nat) returns (r: Result<()>) {
    var res :- Signature.KeyGen(s);
    var _ :- RequireGoodKeyLengths(s, res);
    var public, secret := res.verificationKey, res.signingKey;
    // This is the declared postcondition of the natively implemented KenGen method, plus a condition
    // about zero-padding:
    var _ :- Require(0 < |secret|);
    var _ :- Require(|public| == 1 + (fieldSize + 7) / 8);  // 1 byte for y; x zero-padded up to the field size
    var _ :- Require(public[0] == 2 || public[0] == 3);  // public key uses y compression
    return Success(());
  }

  method {:test} YCompression384() returns (r: Result<()>) {
    r := YCompression(Signature.ECDSA_P384, 384);
  }

  method {:test} YCompression256() returns (r: Result<()>) {
    r := YCompression(Signature.ECDSA_P256, 256);
  }

  method VerifyMessage(params: Signature.ECDSAParams) returns (r: Result<()>){
    var message :- UTF8.Encode("Hello, World!");
    var keys :- Signature.KeyGen(params);
    var _ :- RequireGoodKeyLengths(params, keys);

    var digest :- Signature.Digest(params, message);
    var signature :- Signature.Sign(params, keys.signingKey, digest);
    var shouldBeTrue :- Signature.Verify(params, keys.verificationKey, digest, signature);
    var _ :- Require(shouldBeTrue);
    var badDigest :- Signature.Digest(params, message + [1]);
    var shouldBeFalse :- Signature.Verify(params, keys.verificationKey, badDigest, signature);
    var _ :- Require(!shouldBeFalse);
    return Success(());
  }

  method {:test} VerifyMessage384() returns (r: Result<()>) {
    r := VerifyMessage(Signature.ECDSA_P384);
  }

  method {:test} VerifyMessage256() returns (r: Result<()>) {
    r := VerifyMessage(Signature.ECDSA_P256);
  }
}
