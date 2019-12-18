include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "PaddingMode"} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

    // The smallest ciphertext length is defined using PKCS1, where mLen <= k - 11. If mLen == 0 ==> k >= 11
    // k represents the modulus n in octets, so the min value of the modulus n is (strength + 7) / 8 == 11 ==> 81
    // In practice, this number should realistically be 1024 or, more likely, 2048.
    // TODO: Determine if we want to enforce a min value of 2048 (requires updating the SDK specifications)
    newtype {:nativeType "int"} Strength = x | 81 <= x < (0x8000_0000) witness 81

    // Represents the length in octets (bytes) of the hash function output
    const SHA1_HASH_BYTES := 20
    const SHA256_HASH_BYTES := 32
    const SHA384_HASH_BYTES := 48
    const SHA512_HASH_BYTES := 64

    // GetOctet converts the given number of bits to the octet (byte) size that can include all bits
    function method GetOctet(bits : nat) : nat {
      (bits + 7) / 8
    }

    // MinModulusOctets represents the minimum RSA public modulus n in octets (k) that is usable for a given padding
    function method MinModulusOctets(padding : PaddingMode) : nat {
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

    // MaxEncryptionBytes represents the maximum size (in bytes) that plaintextData can be for a given modulus n and
    // padding mode
    function method MaxEncryptionBytes(padding : PaddingMode, modulusN : nat) : nat
      requires GetOctet(modulusN) >= MinModulusOctets(padding)
    {
      match padding {
        // mLen <= k - 11
        case PKCS1 => GetOctet(modulusN) - 11
        // Per  mLen <= k - 2 * hashLengthBytes - 2
        case OAEP_SHA1 => GetOctet(modulusN) - 2 * SHA1_HASH_BYTES - 2
        case OAEP_SHA256 => GetOctet(modulusN) - 2 * SHA256_HASH_BYTES - 2
        case OAEP_SHA384 => GetOctet(modulusN) - 2 * SHA384_HASH_BYTES - 2
        case OAEP_SHA512 => GetOctet(modulusN) - 2 * SHA512_HASH_BYTES - 2
        }
    }

    class {:extern} RSA {
      static method {:extern} GenerateKeyPair(strength : Strength, padding: PaddingMode)
          returns (publicKey : seq<uint8>, privateKey : seq<uint8>)
        requires GetOctet(strength as nat) >= MinModulusOctets(padding)

      static method {:extern} Decrypt(padding : PaddingMode, privateKey : seq<uint8>, cipherText : seq<uint8>)
          returns (res : Result<seq<uint8>>)
        requires |privateKey| > 0
        requires |cipherText| > 0
        // TODO: Validate that the cipherText length == k, the length in octets of the modulus n

      static method {:extern} Encrypt(padding: PaddingMode, publicKey : seq<uint8>, plaintextData : seq<uint8>)
          returns (res : Result<seq<uint8>>)
        requires |publicKey| > 0
        requires |plaintextData| > 0
        // TODO: Validate that the plaintextData length <= MaxEncryptionBytes(padding, modulus from public key)
    }
}
