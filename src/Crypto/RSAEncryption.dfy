include "../StandardLibrary/StandardLibrary.dfy"

//This code must be reviewed, see #18
module {:extern "RSAEncryption"} RSAEncryption {
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    // TODO: Add support for OAEP_SHA384 and OAEP_SHA512
    datatype {:extern "RSAPaddingMode"} RSAPaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256

    // const UINT32_MAX := 0x1_0000_0000 - 1
    newtype {:nativeType "int"} RSABitLength = x | 521 <= x < (0x8000_0000) witness 521 // 521 = lowest bit size to make msg_len_of_rsa_params nonnegative

    // From Bouncy Castle, in RSACoreEngine.cs
    function method RSACoreMsgLen(bits : RSABitLength) : nat {
        (bits as nat - 1) / 8
    }

    const SHA1_DIGEST_LEN := 20
    const SHA256_DIGEST_LEN := 32

    class {:extern "RSA"} RSA {

        static function method msg_len_of_rsa_params(padding : RSAPaddingMode, bits : RSABitLength) : Option<nat> {
                match padding {
                    // From Bouncy Castle, Pkcs1Encoding.cs
                    case PKCS1 => Some(RSACoreMsgLen(bits) - 10)
                    // From Bouncy Castle, OaepEncoding.cs
                    case OAEP_SHA1 => Some(RSACoreMsgLen(bits) - 1 - 2 * SHA1_DIGEST_LEN)
                    case OAEP_SHA256 => Some(RSACoreMsgLen(bits) - 1 - 2 * SHA256_DIGEST_LEN)
                }
            }

        // TODO: make externs to test below predicates

        static predicate method {:axiom} RSAWfCtx (padding: RSAPaddingMode, c : seq<uint8>) // should correspond to a valid RSA ciphertext

        static predicate method {:axiom} RSAWfEK (padding : RSAPaddingMode, ek : seq<uint8>) // should correspond to a valid PEM-encoded encryption key

        static predicate method {:axiom} RSAWfDK (padding : RSAPaddingMode, dk : seq<uint8>) // should correspond to a valid PEM-encoded decryption key

        static predicate method {:axiom} IsRSAKeypair(padding: RSAPaddingMode, ek : seq<uint8>, dk :seq<uint8>) // dk's public key is ek

        // TODO: below should return an option if anything throws.
        static method {:extern "RSAKeygen"} RSAKeygen(bits : RSABitLength, padding: RSAPaddingMode) returns (ek : seq<uint8>, dk : seq<uint8>)
            ensures RSAWfEK(bits, padding, ek)
            ensures RSAWfDK(bits, padding, dk)
            ensures IsRSAKeypair(bits, padding, ek, dk)

        static function method {:extern "RSADecrypt"} RSADecrypt(bits : RSABitLength, padding : RSAPaddingMode, dk : seq<uint8>, c : seq<uint8>) : Option<seq<uint8>>
            // requires RSAWfCtx(bits, padding, c) -- there should be a runtime way to establish this. or maybe not?
            requires RSAWfDK(bits, padding, dk) // similarly how should I validate the key is well formed

        static method {:extern "RSAEncrypt"} RSAEncrypt(bits : RSABitLength, padding: RSAPaddingMode, ek : seq<uint8>, msg : seq<uint8>) returns (c : Option<seq<uint8>>)
            requires RSAWfEK(bits, padding, ek) // todo: be able to validate this at runtime
            ensures c.Some? ==> RSAWfCtx(bits,padding, c.get)
            ensures c.Some? ==> forall dk :: IsRSAKeypair(bits,padding,ek, dk) ==> RSAWfDK(bits,padding,dk) ==> RSADecrypt(bits, padding, dk, c.get) == Some(msg)
        
        static method {:extern "StringToPEM"} StringToPEM(privatePEM: string, publicPEM: string) returns (ek : seq<uint8>, dk : seq<uint8>)
            ensures RSAWfEK(padding, ek)
            ensures RSAWfDK(padding, dk)
            ensures IsRSAKeypair(padding, ek, dk)
    }

}
