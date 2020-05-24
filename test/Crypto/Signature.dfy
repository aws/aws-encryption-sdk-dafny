// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Crypto/Signature.dfy"
include "../../src/Util/UTF8.dfy"

module TestSignature {
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

      var signature :- expect Signature.Sign(params, keys.signingKey, message);
      var shouldBeTrue :- expect Signature.Verify(params, keys.verificationKey, message, signature);
      expect shouldBeTrue;

      var shouldBeFalse :- expect Signature.Verify(params, keys.verificationKey, message + [1], signature);
      expect !shouldBeFalse;
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
}
