// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Aws.Crypto  

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
  trait {:termination false} Key extends Crypto.IKey {
    ghost var Repr: set<object>
    const strength: StrengthBits
    const padding: PaddingMode
    const pem: seq<uint8>
    predicate Valid()
    {
      |pem| > 0 &&
      GetBytes(strength) >= MinStrengthBytes(padding) &&
      PEMGeneratedWithStrength(pem, strength) &&
      PEMGeneratedWithPadding(pem, padding)
    }
  }

  // These predicates are used to ensure that the pem is tied to a specific strength and padding and will fail if
  // the pem is created with a strength/ padding and any component is then changed
  predicate {:axiom} PEMGeneratedWithStrength(pem: seq<uint8>, strength: StrengthBits)
  predicate {:axiom} PEMGeneratedWithPadding(pem: seq<uint8>, padding: PaddingMode)

  // PrivateKey represents an extension of Key for RSA private keys to aid with type safety
  class PrivateKey extends Key, Crypto.IKey {
    constructor(pem: seq<uint8>, strength: StrengthBits, padding: PaddingMode)
    requires |pem| > 0
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    requires PEMGeneratedWithStrength(pem, strength)
    requires PEMGeneratedWithPadding(pem, padding)
    ensures this.pem == pem
    ensures this.strength == strength
    ensures this.padding == padding
    ensures Valid()
    {
      this.pem := pem;
      this.strength := strength;
      this.padding := padding;
    }
  }

  // PublicKey represents an extension of Key for RSA public keys to aid with type safety
  class PublicKey extends Key, Crypto.IKey {
    constructor(pem: seq<uint8>, strength: StrengthBits, padding: PaddingMode)
    requires |pem| > 0
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    requires PEMGeneratedWithStrength(pem, strength)
    requires PEMGeneratedWithPadding(pem, padding)
    ensures this.pem == pem
    ensures this.strength == strength
    ensures this.padding == padding
    ensures Valid()
    {
      this.pem := pem;
      this.strength := strength;
      this.padding := padding;
    }
  }

  // Represents the length in octets (bytes) of the hash function output
  const SHA1_HASH_BYTES := 20
  const SHA256_HASH_BYTES := 32
  const SHA384_HASH_BYTES := 48
  const SHA512_HASH_BYTES := 64

  // GetBytes converts a bit strength into the octet (byte) size that can include all bits
  function method GetBytes(bits: StrengthBits): nat {
    (bits as nat + 7) / 8
  }

  // MinStrengthBytes represents the minimum strength (in bytes) required for a given padding
  function method MinStrengthBytes(padding: PaddingMode): nat {
    match padding {
      // 0 = k - 11 ==> k = 11
      case PKCS1 => 11
      // 0 = k - 2 * hashLengthBytes - 2 ==> k = 2 + 2 * hashLengthBytes
      case OAEP_SHA1 => 2 * SHA1_HASH_BYTES + 2
      case OAEP_SHA256 => 2 * SHA256_HASH_BYTES + 2
      case OAEP_SHA384 => 2 * SHA384_HASH_BYTES + 2
      case OAEP_SHA512 => 2 * SHA512_HASH_BYTES + 2
      }
  }

  // MaxPlaintextBytes represents the maximum size (in bytes) that the plaintext data can be for a given strength
  // (in bits) and padding mode
  function MaxPlaintextBytes(padding: PaddingMode, strength: StrengthBits): nat
    requires GetBytes(strength) >= MinStrengthBytes(padding)
  {
    match padding {
      // mLen <= k - 11
      case PKCS1 => GetBytes(strength) - 11
      // Per  mLen <= k - 2 * hashLengthBytes - 2
      case OAEP_SHA1 => GetBytes(strength) - 2 * SHA1_HASH_BYTES - 2
      case OAEP_SHA256 => GetBytes(strength) - 2 * SHA256_HASH_BYTES - 2
      case OAEP_SHA384 => GetBytes(strength) - 2 * SHA384_HASH_BYTES - 2
      case OAEP_SHA512 => GetBytes(strength) - 2 * SHA512_HASH_BYTES - 2
      }
  }

  method GenerateKeyPair(strength: StrengthBits, padding: PaddingMode)
      returns (publicKey: PublicKey, privateKey: PrivateKey)
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    ensures privateKey.Valid()
    ensures privateKey.strength == strength
    ensures privateKey.padding == padding
    ensures publicKey.Valid()
    ensures publicKey.strength == strength
    ensures publicKey.padding == padding
    ensures GetBytes(publicKey.strength) >= MinStrengthBytes(publicKey.padding)
    ensures GetBytes(privateKey.strength) >= MinStrengthBytes(privateKey.padding)
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(strength, padding);
    privateKey := new PrivateKey(pemPrivate, strength, padding);
    publicKey := new PublicKey(pemPublic, strength, padding);
  }

  method Decrypt(padding: PaddingMode, privateKey: PrivateKey, cipherText: seq<uint8>) returns (res: Result<seq<uint8>, string>)
    requires privateKey.Valid()
    requires 0 < |cipherText|
    requires padding == privateKey.padding
    // Ideally, we'd be able to make a statement like "requires|cipherText| <= GetBytes(privateKey.strength)", which
    // corresponds to a valid requirement for RSA decryption. However, the expectation for Decrypt is that it can be
    // called in other cases, and error handling needs to be performed for failures. The only way to properly validate
    // this requirement would be to:
    // 1. Make privateKey.strength non-ghost and only call Decrypt inside an if statement when this case is true
    // 2. Pass the requirement up the call chain to the initial user input, ensuring the cipherText size is valid before
    //    even attempting any keychain OnDecrypt operations
    // 3. Turn this requirement into a post-condition similar to "ensures res.Success? => |cipherText| <= GetBytes(privateKey.strength)"
    //    This, in turn, cannot be properly validated because the action is being performed by an extern and provides
    //    minimal value to a customer interacting with this method
    // Therefore, we are intentionally excluding this statement
    ensures privateKey.Valid()
  {
    res := DecryptExtern(padding, privateKey.pem, cipherText);
  }

  method Encrypt(padding: PaddingMode, publicKey: PublicKey, plaintextData: seq<uint8>) returns (res: Result<seq<uint8>, string>)
    requires publicKey.Valid()
    requires GetBytes(publicKey.strength) >= MinStrengthBytes(padding)
    requires 0 < |plaintextData|
    requires padding == publicKey.padding
    // Ideally, we'd be able to make a statement like "|plaintextData| <= MaxPlaintextBytes(padding, publicKey.strength)",
    // which corresponds to a valid requirement for RSA encryption. However, the expectation for Encrypt is that it can be
    // called in other cases, and error handling needs to be performed for failures. The only way to properly validate
    // this requirement would be to:
    // 1. Make publicKey.strength non-ghost and only call Encrypt inside an if statement when this case is true
    // 2. Pass the requirement up the call chain to the initial user input, ensuring the plaintextData size is valid before
    //    even attempting any keychain OnEncrypt operations
    // 3. Turn this requirement into a post-condition similar to
    //    "ensures res.Success? => |plaintextData| <= MaxPlaintextBytes(padding, publicKey.strength)"
    //    This, in turn, cannot be properly validated because the action is being performed by an extern and provides
    //    minimal value to a customer interacting with this method
    // Therefore, we are intentionally excluding this statement
    ensures publicKey.Valid()
  {
    res := EncryptExtern(padding, publicKey.pem, plaintextData);
  }

  // The full extern name needs to be specified here (and below) to prevent conflicts when resolving the extern
  // Note: Customers should call GenerateKeyPair instead of GenerateKeyPairExtern to ensure type safety and additional
  // verification
  method {:extern "RSAEncryption.RSA", "GenerateKeyPairExtern"} GenerateKeyPairExtern(strength: StrengthBits,
                                                                                      padding: PaddingMode)
      returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    ensures |publicKey| > 0
    ensures |privateKey| > 0
    // Tie the public and private keys to a strength and padding to ensure validation fails if they are later changed
    ensures PEMGeneratedWithStrength(publicKey, strength)
    ensures PEMGeneratedWithStrength(privateKey, strength)
    ensures PEMGeneratedWithPadding(publicKey, padding)
    ensures PEMGeneratedWithPadding(privateKey, padding)


  method {:extern "RSAEncryption.RSA", "ParsePemExtern"} ParsePemExtern(
    pem: seq<string>,
    strength: StrengthBits,
    padding: PaddingMode
  ) returns (res: Result<seq<uint8>, string>)
    ensures res.Success? ==> PEMGeneratedWithStrength(res.value, strength)
    ensures res.Success? ==> PEMGeneratedWithPadding(res.value, padding)
    ensures res.Success? ==> |res.value| > 0

  
  // Note: Customers should call Decrypt instead of DecryptExtern to ensure type safety and additional
  // verification
  method {:extern "RSAEncryption.RSA", "DecryptExtern"} DecryptExtern(padding: PaddingMode, privateKey: seq<uint8>,
                                                                      cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |privateKey| > 0
    requires |cipherText| > 0


  // Note: Customers should call Encrypt instead of EncryptExtern to ensure type safety and additional
  // verification
  method {:extern "RSAEncryption.RSA", "EncryptExtern"} EncryptExtern(padding: PaddingMode, publicKey: seq<uint8>,
                                                                      plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
}
