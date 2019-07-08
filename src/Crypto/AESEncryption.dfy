include "../Util/StandardLibrary.dfy"
include "Cipher.dfy"
include "EncryptionDefs.dfy"

module {:extern "AESEncryption"} AESEncryption {
    import opened EncDefs
    import C = Cipher
    import opened StandardLibrary

    class {:extern "AES_GCM"} AES {

        static predicate AESWfCtx(cipher : C.CipherParams, ctx : Ctx) {
            |ctx.c| > (cipher.ivLen) as int
        }

        static predicate AESWfEK (cipher : C.CipherParams, ek : EncryptionKey) {
            |ek.k| == C.KeyLengthOfCipher(cipher) as int
        }

        static predicate AESWfDK (cipher : C.CipherParams, dk : DecryptionKey) {
            |dk.k| == C.KeyLengthOfCipher(cipher) as int
        }

        static predicate IsAESKeypair(ek : EncryptionKey, dk : DecryptionKey) 
        {
            ek.k == dk.k
        }

        static method AESKeygen(cipher : C.CipherParams) returns (ek : EncryptionKey, dk : DecryptionKey)
            ensures AESWfEK(cipher, ek)
            ensures AESWfDK(cipher, dk)
            ensures IsAESKeypair(ek, dk) {
            var k := C.GenKey(cipher);
            ek := EK(k);
            dk := DK(k);
        }



        static function method {:extern "aes_decrypt_impl"} aes_decrypt_impl(cipher : C.CipherParams, taglen : byte, key : seq<byte>, ctxt : seq<byte>, iv : seq<byte>, aad : seq<byte>) : Option<seq<byte>>
            requires |key| == C.KeyLengthOfCipher(cipher) as int

        static function method AESDecrypt(cipher : C.CipherParams, dk : DecryptionKey, md : MData, c : Ctx) : Option<Msg>
            requires AESWfDK(cipher, dk)
            requires AESWfCtx(cipher, c) {
            match aes_decrypt_impl(cipher, cipher.tagLen, dk.k, c.c[cipher.ivLen ..], c.c[0 .. cipher.ivLen], md.md)
                case None => None
                case Some(m) => Some(Msg(m))
            }

        // TODO: make option because BC might fail; get rid of redundant info
        static method {:extern "aes_encrypt"} aes_encrypt_impl(cipher : C.CipherParams, iv : seq<byte>, key : seq<byte>, msg : seq<byte>, md : seq<byte>) returns (ctx : Option<seq<byte>>)
            requires |iv| == cipher.ivLen as int
            requires |key| == C.KeyLengthOfCipher(cipher) as int
            ensures ctx.Some? ==> |ctx.get| > (cipher.ivLen) as int
            ensures ctx.Some? ==> aes_decrypt_impl(cipher, cipher.tagLen, key, ctx.get, iv, md) == Some((msg))

        static method AESEncrypt(cipher : C.CipherParams, ek : EncryptionKey, msg : Msg, md : MData) returns (c : Option<Ctx>)
            requires AESWfEK(cipher,ek)
            ensures c.Some? ==> AESWfCtx(cipher, c.get)
            ensures c.Some? ==> forall dk :: IsAESKeypair(ek, dk) ==> AESDecrypt(cipher, dk, md, c.get) == Some(msg)
            {
                var iv := C.GenIV(cipher);
                var ctx := aes_encrypt_impl(cipher, iv, ek.k, msg.m, md.md);
                match ctx {
                    case None => c := None;
                    case Some(ct) => c := Some(Ctx(iv + ct));
                }
            }
    }
}