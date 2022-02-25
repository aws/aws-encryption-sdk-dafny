// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Signature"} Signature {
  export
    reveals SignatureKeyPair
    reveals ECDSAParams, ECDSAParams.SignatureLength, ECDSAParams.FieldSize
    provides KeyGen, Sign, Verify, IsSigned, IsValidSignatureKeyPair
    provides Wrappers, UInt

  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  predicate {:axiom} IsSigned(key: seq<uint8>, msg: seq<uint8>, signature: seq<uint8>)

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

  predicate {:axiom} IsValidSignatureKeyPair(sigKeyPair: SignatureKeyPair)

  method KeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair, string>)
    ensures match res
      case Success(sigKeyPair) =>
        //= compliance/framework/structures.txt#2.3.3.2.5
        //= type=implication
        //# The signing key MUST fit the specification described by the signature
        //# algorithm (algorithm-suites.md#signature-algorithm) included in this
        //# encryption material's algorithm suite (Section 2.3.3.2.1).
        && |sigKeyPair.verificationKey| == s.FieldSize()
        && IsValidSignatureKeyPair(sigKeyPair)
      case Failure(_) => true
  {
    var sigKeyPair :- ExternKeyGen(s);
    if |sigKeyPair.verificationKey| == s.FieldSize() {
      return Success(sigKeyPair);
    } else {
      return Failure("Incorrect verification-key length from ExternKeyGen.");
    }
  }

  method {:extern "Signature.ECDSA", "ExternKeyGen"} ExternKeyGen(s: ECDSAParams)
    returns (res: Result<SignatureKeyPair, string>)
    ensures res.Success? ==> IsValidSignatureKeyPair(res.value)

  method {:extern "Signature.ECDSA", "Sign"} Sign(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>) returns (sig: Result<seq<uint8>, string>)
    ensures sig.Success? ==> IsSigned(key, msg, sig.value)

  method {:extern "Signature.ECDSA", "Verify"} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>) returns (res: Result<bool, string>)
}
