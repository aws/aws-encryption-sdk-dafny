include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "RSAEncryption"} RSAEncryptionDef {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "PaddingMode"} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

    // The smallest ciphertext length is defined using PKCS1, where messageLength <= k - 11 and k represents the length
    // in octets (bytes) of the modulus n. This means that the minimum possible strength in bits can be calculated as:
    // (strength + 7) / 8 - 11 == 0 ==> min strength == 81 in this scenario (where messageLength == 0). In practice,
    // this number should be much higher (at least 1024 or, better, 2048).
    // TODO: Determine if we want to enforce a min value of 2048 bits as the min strength (requires updating the spec)
    newtype {:nativeType "int"} StrengthBits = x | 81 <= x < (0x8000_0000) witness 81

    // Represents the length in octets (bytes) of the hash function output
    const SHA1_HASH_BYTES := 20
    const SHA256_HASH_BYTES := 32
    const SHA384_HASH_BYTES := 48
    const SHA512_HASH_BYTES := 64

    // GetBytes converts the given number of bits to the octet (byte) size that can include all bits
    function method GetBytes(bits : nat) : nat {
      (bits + 7) / 8
    }

    // MinStrengthBytes represents the minimum strength (in bytes) required for a given padding
    function method MinStrengthBytes(padding : PaddingMode) : nat {
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
    function method MaxPlaintextBytes(padding : PaddingMode, strength : nat) : nat
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

    // The full extern name needs to be specified here (and below) to prevent conflicts when resolving the extern
    method {:extern "RSAEncryption.RSA", "GenerateKeyPair"} GenerateKeyPair(strength : StrengthBits, padding: PaddingMode)
        returns (publicKey : seq<uint8>, privateKey : seq<uint8>)
      requires GetBytes(strength as nat) >= MinStrengthBytes(padding)
      ensures |publicKey| > 0
      ensures |privateKey| > 0
      //ensures |privateKey.pem| > 0
      //ensures privateKey.strength = strength

    method {:extern "RSAEncryption.RSA", "Decrypt"} Decrypt(padding : PaddingMode, privateKey : seq<uint8>,
                                                            cipherText : seq<uint8>)
        returns (res : Result<seq<uint8>>)
      requires |privateKey| > 0
      // requires GetBytes(privateKey.strength) >= |cipherText|
      requires |cipherText| > 0
      // TODO: Validate that the cipherText length == k, the length in octets of the modulus n

    method {:extern "RSAEncryption.RSA", "Encrypt"} Encrypt(padding: PaddingMode, publicKey : seq<uint8>,
                                                            plaintextData : seq<uint8>)
        returns (res : Result<seq<uint8>>)
      requires |publicKey| > 0
      requires |plaintextData| > 0
     // requires |plaintextData| <= MaxPlaintextBytes(publicKey.strength, padding)
      // TODO: Validate that the plaintextData length <= MaxPlaintextBytes(padding, modulus from public key)
}
