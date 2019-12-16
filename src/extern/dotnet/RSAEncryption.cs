using System.Text;
using System;
using System.IO;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Prng;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Asn1.X9;

using byteseq = Dafny.Sequence<byte>;

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

        public static void RSAKeygen(int bits, RSAPaddingMode padding, out byteseq ek, out byteseq dk) {
                RsaKeyPairGenerator gen = new RsaKeyPairGenerator();
                SecureRandom rng = new SecureRandom();
                gen.Init(new RsaKeyGenerationParameters(BigInteger.ValueOf(RSA_PUBLIC_EXPONENT), rng, bits, RSA_CERTAINTY));
                AsymmetricCipherKeyPair kp = gen.GenerateKeyPair();
                byte[] e;
                byte[] d;
                get_pem(kp, out e, out d);
                ek = byteseq.FromArray(e);
                dk = byteseq.FromArray(d);
        }

        public static void StringToPEM(Dafny.Sequence<char> privatePEM, Dafny.Sequence<char> publicPEM, out byteseq ek, out byteseq dk) {
                PemReader pr1 = new PemReader(new StringReader(new string(privatePEM.Elements)));
                Console.WriteLine(new string(privatePEM.Elements));
                AsymmetricKeyParameter privateKey = (AsymmetricKeyParameter) pr1.ReadObject();
                                    Console.WriteLine("foo");

                PemReader pr2 = new PemReader(new StringReader(new string(privatePEM.Elements)));
                AsymmetricKeyParameter publicKey = (AsymmetricKeyParameter)pr2.ReadObject();
                    Console.WriteLine("foo");
                    Console.WriteLine(publicKey);
                byte[] e;
                using (var stringWriter = new StringWriter()) {

                    var pemWriter = new PemWriter(stringWriter);
                    pemWriter.WriteObject(publicKey);
                    e = Encoding.UTF8.GetBytes(stringWriter.ToString());
                }
                ek = byteseq.FromArray(e);

                byte[] d;
                using (var stringWriter = new StringWriter()) {
                    var pemWriter = new PemWriter(stringWriter);
                    pemWriter.WriteObject(privateKey);
                    d = Encoding.UTF8.GetBytes(stringWriter.ToString());
                }
                dk = byteseq.FromArray(d);
        }

        public static STL.Option<byteseq> RSAEncrypt(int bits, RSAPaddingMode padding, byteseq ek, byteseq msg) {
            try {
                AsymmetricKeyParameter pub;
                using (var stringReader = new StringReader(Encoding.UTF8.GetString(ek.Elements)))
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
                return new STL.Option_Some<byteseq>(byteseq.FromArray(engine.ProcessBlock(msg.Elements, 0, msg.Elements.Length)));
            }
            catch {
                return new STL.Option_None<byteseq>();
            }

        }

        // https://stackoverflow.com/questions/28086321/c-sharp-bouncycastle-rsa-encryption-with-public-private-keys

        public static STL.Option<byteseq> RSADecrypt(int bits, RSAPaddingMode padding, byteseq dk, byteseq ctx) {
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

                using ( var txtreader = new StringReader(Encoding.UTF8.GetString(dk.Elements))) {
                    keyPair = (AsymmetricCipherKeyPair) new PemReader(txtreader).ReadObject();
                    engine.Init(false, keyPair.Private);
                }
                return new STL.Option_Some<byteseq>(byteseq.FromArray(engine.ProcessBlock(ctx.Elements, 0, ctx.Elements.Length)));
            }
            catch {
                return new STL.Option_None<byteseq>();
            }
        }
    }
}
