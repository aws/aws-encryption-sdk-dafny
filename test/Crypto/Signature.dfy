include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"

module TestSignature {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Signature

  method YCompression(s: Signature.ECDSAParams) returns (r: Result<()>) {
    var res := Signature.ECDSA.KeyGen(s);
    if res == None {
      return Failure("KeyGen failed");
    }
    var (public, secret) := res.get;
    // This is the declared postcondition of the natively implemented KenGen method:
    var _ :- Require(0 < |public|);
    var _ :- Require(0 < |secret|);
    var _ :- Require(public[0] == 2 || public[0] == 3);  // public key uses y compression
    return Success(());
  }

  method {:test} YCompression384() returns (r: Result<()>) {
    r := YCompression(Signature.ECDSA_P384);
  }

  method {:test} YCompression256() returns (r: Result<()>) {
    r := YCompression(Signature.ECDSA_P256);
  }
}
