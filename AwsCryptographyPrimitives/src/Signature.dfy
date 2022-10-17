// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module {:extern "Signature"} Signature {
  // TODO figure out how to add the export sets back in
  // export
  //   reveals SignatureKeyPair
  //   reveals ECDSAParams, ECDSAParams.SignatureLength, ECDSAParams.FieldSize
  //   provides KeyGen, Sign, Verify, IsSigned, IsValidSignatureKeyPair
  //   provides Wrappers, UInt, Types

  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  predicate {:axiom} IsSigned(key: seq<uint8>, msg: seq<uint8>, signature: seq<uint8>)

  function method SignatureLength(signatureAlgorithm: Types.ECDSASignatureAlgorithm): uint16 {
    match signatureAlgorithm
    case ECDSA_P256 => 71
    case ECDSA_P384 => 103
  }

  function method FieldSize(signatureAlgorithm: Types.ECDSASignatureAlgorithm): nat {
    match signatureAlgorithm
    case ECDSA_P256 => assert 1 + (256 + 7) / 8 == 33; 33
    case ECDSA_P384 => assert 1 + (384 + 7) / 8 == 49; 49
  }

  predicate {:axiom} IsValidSignatureKeyPair(sigKeyPair: SignatureKeyPair)

  method KeyGen(input: Types.GenerateECDSASignatureKeyInput) returns (res: Result<Types.GenerateECDSASignatureKeyOutput, Types.Error>)
    ensures match res
      case Success(sigKeyPair) =>
        //= compliance/framework/structures.txt#2.3.3.2.5
        //= type=implication
        //# The signing key MUST fit the specification described by the signature
        //# algorithm (algorithm-suites.md#signature-algorithm) included in this
        //# encryption material's algorithm suite (Section 2.3.3.2.1).
        && |sigKeyPair.verificationKey| == FieldSize(input.signatureAlgorithm)
        // && IsValidSignatureKeyPair(sigKeyPair)
      case Failure(_) => true
  {
    var sigKeyPair :- ExternKeyGen(input.signatureAlgorithm);

    :- Need(|sigKeyPair.verificationKey| == FieldSize(input.signatureAlgorithm),
      Types.AwsCryptographicPrimitivesError(
        message := "Incorrect verification-key length from ExternKeyGen."
      ));

    return Success(Types.GenerateECDSASignatureKeyOutput(
      signatureAlgorithm := input.signatureAlgorithm,
      verificationKey := sigKeyPair.verificationKey,
      signingKey := sigKeyPair.signingKey
    ));
  }

  method {:extern "Signature.ECDSA", "ExternKeyGen"} ExternKeyGen(s: Types.ECDSASignatureAlgorithm)
    returns (res: Result<SignatureKeyPair, Types.Error>)
    ensures res.Success? ==> IsValidSignatureKeyPair(res.value)

  method {:extern "Signature.ECDSA", "Sign"} Sign(s: Types.ECDSASignatureAlgorithm, key: seq<uint8>, msg: seq<uint8>)
    returns (sig: Result<seq<uint8>, Types.Error>)
    ensures sig.Success? ==> IsSigned(key, msg, sig.value)

  // This is a valid function
  // because the same inputs will result in the same outputs.
  function method {:extern "Signature.ECDSA", "Verify"} Verify(s: Types.ECDSASignatureAlgorithm, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>)
    : (res: Result<bool, Types.Error>)
}
