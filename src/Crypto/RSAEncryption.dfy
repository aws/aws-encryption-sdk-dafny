include "../StandardLibrary/StandardLibrary.dfy"
include "Cipher.dfy"
include "EncryptionDefs.dfy"

module {:extern "RSAEncryption"} RSAEncryption {
    import opened EncDefs
    import C = Cipher
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    datatype {:extern "RSAPaddingMode"} RSAPaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256

    // const UINT32_MAX := 0x1_0000_0000 - 1
    newtype RSABitLength = x | 521 <= x < (0x1_0000_0000) witness 521 // 521 = lowest bit size to make msg_len_of_rsa_params nonnegative

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

        static predicate {:axiom} RSAWfCtx (bits : RSABitLength, padding: RSAPaddingMode, c : Ctx) // should correspond to a valid RSA ciphertext

        static predicate {:axiom} RSAWfEK (bits : RSABitLength, padding : RSAPaddingMode, ek : EncryptionKey) // should correspond to a valid PEM-encoded encryption key

        static predicate {:axiom} RSAWfDK (bits : RSABitLength, padding : RSAPaddingMode, dk : DecryptionKey) // should correspond to a valid PEM-encoded decryption key

        static predicate {:axiom} IsRSAKeypair(bits : RSABitLength, padding: RSAPaddingMode, ek : EncryptionKey, dk :DecryptionKey) // dk's public key is ek

        static method {:extern "RSAKeygen"} RSAKeygen(bits : RSABitLength, padding: RSAPaddingMode) returns (ek : EncryptionKey, dk : DecryptionKey)
            ensures RSAWfEK(bits, padding, ek)
            ensures RSAWfDK(bits, padding, dk)
            ensures IsRSAKeypair(bits, padding, ek, dk)

        static function method {:extern "RSADecrypt"} RSADecrypt(bits : RSABitLength, padding : RSAPaddingMode, dk : DecryptionKey, md : MData, c : Ctx) : Option<Msg>
            requires RSAWfDK(bits, padding, dk)
            requires RSAWfCtx(bits, padding, c)

        static method {:extern "RSAEncrypt"} RSAEncrypt(bits : RSABitLength, padding: RSAPaddingMode, ek : EncryptionKey, msg : Msg, md : MData) returns (c : Option<Ctx>)
            requires RSAWfEK(bits, padding, ek)
            ensures c.Some? ==> RSAWfCtx(bits,padding, c.get)
            ensures c.Some? ==> forall dk :: IsRSAKeypair(bits,padding,ek, dk) ==> RSAWfDK(bits,padding,dk) ==> RSADecrypt(bits, padding, dk, md, c.get) == Some(msg)

    }

}