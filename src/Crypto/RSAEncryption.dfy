// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  //= compliance/framework/raw-rsa-keyring.txt#2.5.1.1
  //= type=implication
  //# This keyring MUST NOT use a padding scheme outside those defined
  //# above.
  datatype {:extern "PaddingMode"} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

  //= compliance/framework/raw-rsa-keyring.txt#2.5.1
  //= type=TODO
  //# If the padding scheme uses MGF1 Padding, the hash function used as
  //# part of MGF1 MUST be the same hash function used to hash the
  //# plaintext data key.
  // NOTE: this file currently does not mention MGF1 at all!

  // The smallest ciphertext length is defined using PKCS1, where messageLength <= k - 11 and k represents the strength,
  // defined as the length in octets (bytes) of the modulus n. This means that the minimum possible strength in bits
  // can be calculated as: (strength + 7) / 8 - 11 == 0 ==> min strength == 81 in this scenario
  // (where messageLength == 0). In practice, this number should be much higher (at least 1024 or, better, 2048).
  // TODO: Determine if we want to enforce a min value of 2048 bits as the min strength (requires updating the spec)
  newtype {:nativeType "int", "number"} StrengthBits = x | 81 <= x < (0x8000_0000) witness 81

  // This trait represents the parent for RSA public and private keys
  trait {:termination false} Key {
    const strength: StrengthBits
    const pem: seq<uint8>
    predicate Valid()
    {
      |pem| > 0
    }
  }

  // PrivateKey represents an extension of Key for RSA private keys to aid with type safety
  class PrivateKey extends Key {
    constructor(pem: seq<uint8>, strength: StrengthBits)
    requires |pem| > 0
    ensures this.pem == pem
    ensures this.strength == strength
    ensures Valid()
    {
      this.pem := pem;
      this.strength := strength;
    }
  }

  // PublicKey represents an extension of Key for RSA public keys to aid with type safety
  class PublicKey extends Key {
    constructor(pem: seq<uint8>, strength: StrengthBits)
    requires |pem| > 0
    ensures this.pem == pem
    ensures this.strength == strength
    ensures Valid()
    {
      this.pem := pem;
      this.strength := strength;
    }
  }

  method GenerateKeyPair(strength: StrengthBits)
    returns (publicKey: PublicKey, privateKey: PrivateKey)
    requires strength <= 15360
    ensures privateKey.Valid()
    ensures publicKey.Valid()
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(strength);
    privateKey := new PrivateKey(pemPrivate, strength);
    publicKey := new PublicKey(pemPublic, strength);
  }

  // The full extern name needs to be specified here (and below) to prevent conflicts when resolving the extern
  // Note: Customers should call GenerateKeyPair instead of GenerateKeyPairExtern to ensure type safety and additional
  // verification
  method {:extern "RSAEncryption.RSA", "GenerateKeyPairExtern"} GenerateKeyPairExtern(strength: StrengthBits)
      returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    ensures |publicKey| > 0
    ensures |privateKey| > 0
    // Tie the public and private keys to a strength and padding to ensure validation fails if they are later changed

  method {:extern "RSAEncryption.RSA", "DecryptExtern"} DecryptExtern(padding: PaddingMode, privateKey: seq<uint8>,
                                                                      cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |privateKey| > 0
    requires |cipherText| > 0

  method {:extern "RSAEncryption.RSA", "EncryptExtern"} EncryptExtern(padding: PaddingMode, publicKey: seq<uint8>,
                                                                      plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
}
