using System;
using System.Security.Cryptography;
using System.Text;
using System.IO;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Modes;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Prng;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;

using byteseq = Dafny.Sequence<byte>;

namespace AESEncryption {

    public partial class AES_GCM {

        public static STL.Option<byteseq> aes_encrypt(Cipher.CipherParams p, byteseq iv, byteseq key, byteseq msg, byteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(new KeyParameter(key.Elements), (int)p.tagLen * 8, iv.Elements, aad.Elements);
                cipher.Init(true, param);

                byte[] c = new byte[cipher.GetOutputSize(msg.Elements.Length)];
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, c, 0);
                cipher.DoFinal(c, len);
                return new STL.Option_Some<byteseq>(new byteseq(c));
            }
            catch {
                return new STL.Option_None<byteseq>();
            }
        }

        public static STL.Option<byteseq> aes_decrypt_impl(Cipher.CipherParams p, byte taglen, byteseq key, byteseq ctx, byteseq iv, byteseq aad) {
            var cipher = new GcmBlockCipher(new AesEngine());
            var param = new AeadParameters(new KeyParameter(key.Elements), taglen * 8, iv.Elements, aad.Elements);
            cipher.Init(false, param);
            var pt = new byte[cipher.GetOutputSize(ctx.Elements.Length)];
            try {
                var len = cipher.ProcessBytes(ctx.Elements, 0, ctx.Elements.Length, pt, 0);
                cipher.DoFinal(pt, len);
            }
            catch {
                return new STL.Option_None<byteseq>();
            }
            return new STL.Option_Some<byteseq>(new byteseq(pt));
        }
    }
}
 //  https://stackoverflow.com/questions/23056347/creating-rsa-public-private-key-pair-with-bouncy-castle-or-net-rsacryptoservice

namespace RSAEncryption {

    public partial class RSA {

        public static void get_pem(AsymmetricCipherKeyPair kp, out byte[] pk, out byte[] sk) {
            using (var stringWriter = new StringWriter()) {
                var pemWriter = new PemWriter(stringWriter);
                pemWriter.WriteObject(kp.Public);
                pk = Encoding.UTF8.GetBytes(stringWriter.ToString());
            }

            using (var stringWriter = new StringWriter()) {
                var pemWriter = new PemWriter(stringWriter);
                pemWriter.WriteObject(kp.Private);
                sk = Encoding.UTF8.GetBytes(stringWriter.ToString());
            }
        }

        const int RSA_PUBLIC_EXPONENT = (65537);
        const int RSA_CERTAINTY = 256;

        public static void RSAKeygen(ulong bits, RSAPaddingMode padding, out EncDefs.EncryptionKey ek, out EncDefs.DecryptionKey dk) {
                RsaKeyPairGenerator gen = new RsaKeyPairGenerator();
                SecureRandom rng = new SecureRandom();
                gen.Init(new RsaKeyGenerationParameters(BigInteger.ValueOf(RSA_PUBLIC_EXPONENT), rng, 2048, RSA_CERTAINTY));
                AsymmetricCipherKeyPair kp = gen.GenerateKeyPair();
                byte[] e;
                byte[] d;
                get_pem(kp, out e, out d);
                ek = new EncDefs.EncryptionKey(new byteseq(e));
                dk = new EncDefs.DecryptionKey(new byteseq(d));
        }

        public static STL.Option<EncDefs.Ctx> RSAEncrypt(ulong bits, RSAPaddingMode padding, EncDefs.EncryptionKey ek, EncDefs.Msg msg, EncDefs.MData md) {
            try {
                AsymmetricKeyParameter pub;
                using (var stringReader = new StringReader(Encoding.UTF8.GetString(ek.k.Elements)))
                {
                    var pemReader = new PemReader(stringReader);
                    var pemObject = pemReader.ReadObject();
                    pub = ((AsymmetricKeyParameter)pemObject);
                }

                IAsymmetricBlockCipher engine;

                if (padding.is_PKCS1) {
                    engine = new Pkcs1Encoding(new RsaEngine());
                } else if (padding.is_OAEP__SHA1) {
                    engine = new OaepEncoding(new RsaEngine(), new Sha1Digest());
                }
                else { // paddingi_is_OAEP__SHA256
                    engine = new OaepEncoding(new RsaEngine(), new Sha256Digest());
                }

                engine.Init(true, pub);
                return new STL.Option_Some<EncDefs.Ctx>(new EncDefs.Ctx(new byteseq(engine.ProcessBlock(msg.m.Elements, 0, msg.m.Elements.Length))));
            }
            catch {
                return new STL.Option_None<EncDefs.Ctx>();
            }

        }

        // https://stackoverflow.com/questions/28086321/c-sharp-bouncycastle-rsa-encryption-with-public-private-keys

        public static STL.Option<EncDefs.Msg> RSADecrypt(ulong bits, RSAPaddingMode padding, EncDefs.DecryptionKey dk, EncDefs.MData md, EncDefs.Ctx ctx) {
            try {
                AsymmetricCipherKeyPair keyPair;

                IAsymmetricBlockCipher engine;

                if (padding.is_PKCS1) {
                    engine = new Pkcs1Encoding(new RsaEngine());
                } else if (padding.is_OAEP__SHA1) {
                    engine = new OaepEncoding(new RsaEngine(), new Sha1Digest(), null);
                }
                else { // paddingi_is_OAEP__SHA256
                    engine = new OaepEncoding(new RsaEngine(), new Sha256Digest(), null);
                }
            
                using ( var txtreader = new StringReader(Encoding.UTF8.GetString(dk.k.Elements))) {
                    keyPair = (AsymmetricCipherKeyPair) new PemReader(txtreader).ReadObject();
                    engine.Init(false, keyPair.Private);
                }
                return new STL.Option_Some<EncDefs.Msg>(new EncDefs.Msg(new byteseq(engine.ProcessBlock(ctx.c.Elements, 0, ctx.c.Elements.Length))));
            }
            catch {
                return new STL.Option_None<EncDefs.Msg>();
            }           
        }
    }
}
