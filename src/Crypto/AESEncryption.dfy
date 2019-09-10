include "../StandardLibrary/StandardLibrary.dfy"
include "Cipher.dfy"

module {:extern "AESEncryption"} AESEncryption {
    import C = Cipher
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    class {:extern "AES_GCM"} AES {

        static predicate method AESWfCtx(cipher : C.CipherParams, ctx : seq<uint8>) {
            |ctx| > (cipher.ivLen) as int
        }

        static predicate method AESWfKey (cipher : C.CipherParams, k : seq<uint8>) {
            |k| == C.KeyLengthOfCipher(cipher) as int
        }

        // TODO: make below return an option if anything throws.
        static method AESKeygen(cipher : C.CipherParams) returns (k : seq<uint8>)
            ensures AESWfKey(cipher, k) {
            k := C.GenKey(cipher);
        }

        static function method {:extern "aes_decrypt"} aes_decrypt(cipher : C.CipherParams, taglen : uint8, key : seq<uint8>, ctxt : seq<uint8>, iv : seq<uint8>, aad : seq<uint8>) : Result<seq<uint8>>
            requires |key| == C.KeyLengthOfCipher(cipher) as int

        static function method AESDecrypt(cipher : C.CipherParams, k : seq<uint8>, md : seq<uint8>, c : seq<uint8>) : Result<seq<uint8>>
            requires AESWfKey(cipher, k)
            requires AESWfCtx(cipher, c) {
            match aes_decrypt(cipher, cipher.tagLen, k, c[cipher.ivLen ..], c[0 .. cipher.ivLen], md)
                case Failure(e) => Failure(e)
                case Success(m) => Success(m)
            }

        static method {:extern "aes_encrypt"} aes_encrypt (cipher : C.CipherParams, 
                                             iv : seq<uint8>, 
                                             key : seq<uint8>, 
                                             msg : seq<uint8>, 
                                             aad : seq<uint8>) 
            returns (ctx : Result<seq<uint8>>)

            requires |iv| == cipher.ivLen as int
            requires |key| == C.KeyLengthOfCipher(cipher) as int
            ensures ctx.Success? ==> |ctx.value| > (cipher.tagLen) as int 
            ensures ctx.Success? ==> aes_decrypt(cipher, cipher.tagLen, key, ctx.value, iv, aad) == Success((msg))

        static method AESEncrypt(cipher : C.CipherParams, k : seq<uint8>, msg : seq<uint8>, md : seq<uint8>) returns (c : Result<seq<uint8>>)
            requires AESWfKey(cipher, k)
            ensures c.Success? ==> AESWfCtx(cipher, c.value)
            ensures c.Success? ==> AESDecrypt(cipher, k, md, c.value) == Success(msg)
            {
                var iv := C.GenIV(cipher);
                var ctx := aes_encrypt(cipher, iv, k, msg, md);
                match ctx {
                    case Failure(e) => return Failure(e);
                    case Success(ct) => return Success(iv + ct);
                }
            }
    }
}