include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Signature"} Signature {
  export
    reveals SignatureKeyPair
    reveals ECDSAParams, ECDSAParams.SignatureLength, ECDSAParams.FieldSize
    provides KeyGen, Sign, Verify
    provides StandardLibrary, UInt

  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  datatype ECDSAParams = ECDSA_P384 | ECDSA_P256
  {
    function method SignatureLength(): uint16 {
      match this
      case ECDSA_P256 => 71
      case ECDSA_P384 => 103
    }

    function method FieldSize(): nat {
      match this
      case ECDSA_P256 => assert 1 + (256 + 7) / 8 == 33; 33
      case ECDSA_P384 => assert 1 + (384 + 7) / 8 == 49; 49
    }
  }

  method KeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair>)
    ensures match res
      case Success(sigKeyPair) => |sigKeyPair.verificationKey| == s.FieldSize()
      case Failure(_) => true
  {
    var sigKeyPair :- ExternKeyGen(s);
    if |sigKeyPair.verificationKey| == s.FieldSize() {
      return Success(sigKeyPair);
    } else {
      return Failure("Incorrect verification-key length from ExternKeyGen.");
    }
  }

  method {:extern "Signature.ECDSA", "ExternKeyGen"} ExternKeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair>)

  method {:extern "Signature.ECDSA", "Sign"} Sign(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>) returns (sig: Result<seq<uint8>>)

  method {:extern "Signature.ECDSA", "Verify"} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>) returns (res: Result<bool>)
}
