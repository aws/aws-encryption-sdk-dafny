include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "PaddingMode"} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

    // The smallest allowed bit lenght represents PKCS1, where modulus octets >= 11, which implies 11 * 8 - 7 = min bits
    newtype {:nativeType "int"} BitLength = x | 81 <= x < (0x8000_0000) witness 81

    // Represents the length in bytes of the hash function output
    const SHA1_HASH_BYTES := 20
    const SHA256_HASH_BYTES := 32
    const SHA384_HASH_BYTES := 48
    const SHA512_HASH_BYTES := 64

    // GetOctet converts the given number of bits to the octet (byte) size that includes all bits
    function method GetOctet(bits : BitLength) : nat {
      (bits as nat + 7) / 8
    }

    // MinRSAModulusOctets represents the minimum RSA public modulus octets that is usable for a given padding mode
    function method MinRSAModulusOctets(padding : PaddingMode) : nat {
      match padding {
        // 0 = minOctets - 11 ==> minOctets = 11
        case PKCS1 => 11
        // 0 = minOctets - 2 * hashLengthBytes - 2 ==> minModulus = 2 + 2 * hashLengthBytes
        case OAEP_SHA1 => 2 * SHA1_HASH_BYTES + 2
        case OAEP_SHA256 => 2 * SHA256_HASH_BYTES + 2
        case OAEP_SHA384 => 2 * SHA384_HASH_BYTES + 2
        case OAEP_SHA512 => 2 * SHA512_HASH_BYTES + 2
        }
    }

    // MaxEncryptionBytes represents the maximum size (in bytes) that plaintextData can be for a given BitLength and
    // padding mode
    function method MaxEncryptionBytes(padding : PaddingMode, n : BitLength) : nat
      requires GetOctet(n) >= MinRSAModulusOctets(padding)
    {
      match padding {
        // mLen <= GetOctet(n) - 11
        case PKCS1 => GetOctet(n) - 11
        // Per  mLen <= GetOctet(n) - 2 * hashLengthBytes - 2
        case OAEP_SHA1 => GetOctet(n) - 2 * SHA1_HASH_BYTES - 2
        case OAEP_SHA256 => GetOctet(n) - 2 * SHA256_HASH_BYTES - 2
        case OAEP_SHA384 => GetOctet(n) - 2 * SHA384_HASH_BYTES - 2
        case OAEP_SHA512 => GetOctet(n) - 2 * SHA512_HASH_BYTES - 2
        }
    }

    method {:extern "RSAEncryption", "GenerateKeyPair"} GenerateKeyPair(bits : BitLength, padding: PaddingMode)
        returns (publicKey : seq<uint8>, privateKey : seq<uint8>)
      requires GetOctet(bits) >= MinRSAModulusOctets(padding)

    method {:extern "RSAEncryption", "Decrypt"} Decrypt(padding : PaddingMode, privateKey : seq<uint8>,
                                                                  cipherText : seq<uint8>)
        returns (res : Result<seq<uint8>>)

    method {:extern "RSAEncryption", "Encrypt"} Encrypt(padding: PaddingMode, publicKey : seq<uint8>,
                                                                  plaintextData : seq<uint8>)
        returns (res : Result<seq<uint8>>)
}
