// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  // The smallest ciphertext length is defined using PKCS1, where messageLength <= k - 11 and k represents the strength,
  // defined as the length in octets (bytes) of the modulus n. This means that the minimum possible strength in bits
  // can be calculated as: (strength + 7) / 8 - 11 == 0 ==> min strength == 81 in this scenario
  // (where messageLength == 0). In practice, this number should be much higher (at least 1024 or, better, 2048).
  // TODO: Determine if we want to enforce a min value of 2048 bits as the min strength (requires updating the spec)
  // newtype {:nativeType "int", "number"} StrengthBits = x | 81 <= x < (0x8000_0000) witness 81

  method GenerateKeyPair(strength: Types.RSAStrengthBits)
      returns (publicKey: Types.RSAPublicKey, privateKey: Types.RSAPrivateKey)
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(strength);
    privateKey := Types.RSAPrivateKey(pem := pemPrivate, strength := strength);
    publicKey := Types.RSAPublicKey(pem := pemPublic, strength := strength);
  }

  method Decrypt(input: Types.RSADecryptInput)
    returns (output: Result<seq<uint8>, Types.Error>)
  {
    :- Need(0 < |input.privateKey| && 0 < |input.cipherText|, Types.AwsCryptographicPrimitivesError( message := ""));
    output := DecryptExtern(input.padding, input.privateKey, input.cipherText);
  }

  method Encrypt(input: Types.RSAEncryptInput)
    returns (output: Result<seq<uint8>, Types.Error>)
  {
    :- Need(0 < |input.publicKey| && 0 < |input.plaintext|, Types.AwsCryptographicPrimitivesError( message := ""));
    output := EncryptExtern(input.padding, input.publicKey, input.plaintext);
  }

  method {:extern "RSAEncryption.RSA", "GenerateKeyPairExtern"} GenerateKeyPairExtern(strength: Types.RSAStrengthBits)
      returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    ensures |publicKey| > 0
    ensures |privateKey| > 0

  method {:extern "RSAEncryption.RSA", "DecryptExtern"} DecryptExtern(padding: Types.RSAPaddingMode, privateKey: seq<uint8>,
                                                                      cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |privateKey| > 0
    requires |cipherText| > 0

  method {:extern "RSAEncryption.RSA", "EncryptExtern"} EncryptExtern(padding: Types.RSAPaddingMode, publicKey: seq<uint8>,
                                                                      plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
}
