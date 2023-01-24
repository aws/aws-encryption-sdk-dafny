// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Signature.dfy"

module TestSignature {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt
  import Types = Aws.Cryptography.Primitives.Types
  import UTF8
  import opened Wrappers
  import Signature

  const P256: Types.ECDSASignatureAlgorithm := Types.ECDSASignatureAlgorithm.ECDSA_P256;
  const P384: Types.ECDSASignatureAlgorithm := Types.ECDSASignatureAlgorithm.ECDSA_P384;

  method RequireGoodKeyLengths(
    alg: Types.ECDSASignatureAlgorithm,
    sigKeyPair: Signature.SignatureKeyPair
  )
  {
    // The following is a declared postcondition of the KeyGen method:
    expect |sigKeyPair.verificationKey| == Signature.FieldSize(alg);
  }

  method YCompression(alg: Types.ECDSASignatureAlgorithm, fieldSize: nat) {
    var res :- expect Signature.ExternKeyGen(alg);
    RequireGoodKeyLengths(alg, res);
    var public, secret := res.verificationKey, res.signingKey;
    // This is the declared postcondition of the natively implemented KenGen method, plus a condition
    // about zero-padding:
    expect 0 < |secret|;
    expect |public| == 1 + (fieldSize + 7) / 8;  // 1 byte for y; x zero-padded up to the field size
    expect public[0] == 2 || public[0] == 3;  // public key uses y compression
  }

  method VerifyMessage(alg: Types.ECDSASignatureAlgorithm) {
    var message :- expect UTF8.Encode("Hello, World!");
    var genInput := Types.GenerateECDSASignatureKeyInput( signatureAlgorithm := alg);
    var keys :- expect Signature.ExternKeyGen(alg);
    RequireGoodKeyLengths(alg, keys);
      
    var signature :- expect Signature.Sign(alg, keys.signingKey, message);
    var shouldBeTrue :- expect Signature.Verify(alg, keys.verificationKey, message, signature);
    expect shouldBeTrue;
      
    var shouldBeFalse :- expect Signature.Verify(alg, keys.verificationKey, message + [1], signature);
    expect !shouldBeFalse;
  }
  
  method {:test} YCompression384() {
    YCompression(P384, 384);
  }

  method {:test} YCompression256() {
    YCompression(P256, 256);
  }

  method {:test} VerifyMessage384() {
    VerifyMessage(P384);
  }

  method {:test} VerifyMessage256() {
    VerifyMessage(P256);
  }
}
