include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"

module TestSignature {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Signature

  method YCompression(s: Signature.ECDSAParams, fieldSize: nat) returns (r: TestResult) {
    var res := Signature.ECDSA.KeyGen(s);
    if res == None {
      return TestFailure("KeyGen failed");
    }
    var (public, secret) := res.get;
    // This is the declared postcondition of the natively implemented KenGen method, plus a condition
    // about zero-padding:
    :- Require(0 < |secret|);
    :- Require(|public| == 1 + (fieldSize + 7) / 8);  // 1 byte for y; x zero-padded up to the field size
    :- Require(public[0] == 2 || public[0] == 3);  // public key uses y compression
    return TestSuccess;
  }

  method {:test} YCompression384() returns (r: TestResult) {
    r := YCompression(Signature.ECDSA_P384, 384);
  }

  method {:test} YCompression256() returns (r: TestResult) {
    r := YCompression(Signature.ECDSA_P256, 256);
  }
}
