include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Signature"} Signature {
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

    method {:extern "Signature.ECDSA", "KeyGen"} KeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair>)
      ensures match res
        case Success(sigKeyPair) => |sigKeyPair.verificationKey| == s.FieldSize()
        case Failure(_) => true

    method {:extern "Signature.ECDSA", "Sign"} Sign(s: ECDSAParams, key: seq<uint8>, digest: seq<uint8>) returns (sig: Result<seq<uint8>>)

    method {:extern "Signature.ECDSA", "Verify"} Verify(s: ECDSAParams, key: seq<uint8>, digest: seq<uint8>, sig: seq<uint8>) returns (res: Result<bool>)

    method {:extern "Signature.ECDSA", "Digest"} Digest(s: ECDSAParams, msg: seq<uint8>) returns (digest: Result<seq<uint8>>)
}
