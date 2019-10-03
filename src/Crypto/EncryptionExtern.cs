using System;
using System.Text;
using System.IO;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.EC;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Modes;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Prng;
using Org.BouncyCastle.Crypto.Signers;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Math.EC;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Asn1.X9;

using byteseq = Dafny.Sequence<byte>;

namespace AESEncryption {
    //TODO This code has yet to be reviewed. See issue #36
    public partial class AES_GCM {

        //FIXME: Ensure that these methods correctly handle authenticaition tags, see #36
        public static STL.Result<byteseq> AESEncrypt(AESUtils.Params p,
                                                      byteseq iv,
                                                      byteseq key,
                                                      byteseq msg,
                                                      byteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(new KeyParameter(key.Elements), (int)p.tagLen * 8, iv.Elements, aad.Elements);
                cipher.Init(true, param);

                byte[] c = new byte[cipher.GetOutputSize(msg.Elements.Length)];
                var len = cipher.ProcessBytes(msg.Elements, 0, msg.Elements.Length, c, 0);
                cipher.DoFinal(c, len);
                return new STL.Result_Success<byteseq>(new byteseq(c));
            }
            catch {
                return new STL.Result_Failure<byteseq>(new Dafny.Sequence<char>("aes encrypt err".ToCharArray()));
            }
        }

        public static STL.Result<byteseq> AESDecrypt(AESUtils.Params p, byteseq key, byteseq ctx, byteseq iv, byteseq aad) {
            try {
                var cipher = new GcmBlockCipher(new AesEngine());
                var param = new AeadParameters(new KeyParameter(key.Elements), p.tagLen * 8, iv.Elements, aad.Elements);
                cipher.Init(false, param);
                var pt = new byte[cipher.GetOutputSize(ctx.Elements.Length)];
                var len = cipher.ProcessBytes(ctx.Elements, 0, ctx.Elements.Length, pt, 0);
                cipher.DoFinal(pt, len);
                return new STL.Result_Success<byteseq>(new byteseq(pt));
            }
            catch {
                // TODO: distinguish BC error from unsuccessful decrypt
                return new STL.Result_Failure<byteseq>(new Dafny.Sequence<char>("aes decrypt err".ToCharArray()));

            }
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

        public static void RSAKeygen(int bits, RSAPaddingMode padding, out byteseq ek, out byteseq dk) {
                RsaKeyPairGenerator gen = new RsaKeyPairGenerator();
                SecureRandom rng = new SecureRandom();
                gen.Init(new RsaKeyGenerationParameters(BigInteger.ValueOf(RSA_PUBLIC_EXPONENT), rng, bits, RSA_CERTAINTY));
                AsymmetricCipherKeyPair kp = gen.GenerateKeyPair();
                byte[] e;
                byte[] d;
                get_pem(kp, out e, out d);
                ek = new byteseq(e);
                dk = new byteseq(d);
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
                return new STL.Option_Some<byteseq>(new byteseq(engine.ProcessBlock(msg.Elements, 0, msg.Elements.Length)));
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
                return new STL.Option_Some<byteseq>(new byteseq(engine.ProcessBlock(ctx.Elements, 0, ctx.Elements.Length)));
            }
            catch {
                return new STL.Option_None<byteseq>();
            }
        }
    }
}

namespace Signature {
    public partial class ECDSA {
        public static STL.Option<_System.Tuple2<byteseq, byteseq>> KeyGen(ECDSAParams x) {
            try {
                ECKeyPairGenerator g = new ECKeyPairGenerator();
                SecureRandom rng = new SecureRandom();
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                    g.Init(new ECKeyGenerationParameters(new ECDomainParameters(p.Curve, p.G, p.N, p.H), rng));
                }
                else { // x is ECDSA__P256
                    p = ECNamedCurveTable.GetByName("secp256r1");
                    g.Init(new ECKeyGenerationParameters(new ECDomainParameters(p.Curve, p.G, p.N, p.H), rng));
                }
                AsymmetricCipherKeyPair kp = g.GenerateKeyPair();
                ECPoint pt = ((ECPublicKeyParameters)kp.Public).Q;
                byteseq vk = new byteseq(pt.GetEncoded());
                byteseq sk = new byteseq(((ECPrivateKeyParameters)kp.Private).D.ToByteArray());
                return new STL.Option_Some<_System.Tuple2<byteseq, byteseq>>(new _System.Tuple2<byteseq, byteseq>(vk, sk));
            }
            catch {
                return new STL.Option_None<_System.Tuple2<byteseq, byteseq>>();
            }
        }

        public static bool Verify(ECDSAParams x, byteseq vk, byteseq msg, _System.Tuple2<byteseq, byteseq> sig) {
            try {
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                }
                else {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                }
                ECDomainParameters dp = new ECDomainParameters(p.Curve, p.G, p.N, p.H);
                ECPoint pt  = p.Curve.DecodePoint(vk.Elements);
                ECPublicKeyParameters vkp = new ECPublicKeyParameters(pt, dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(false, vkp);
                BigInteger r = new BigInteger(sig._0.Elements);
                BigInteger s = new BigInteger(sig._1.Elements);
                return sign.VerifySignature(msg.Elements, r, s);
            }
            catch {
                return false;
            }
        }

        public static STL.Option<_System.Tuple2<byteseq, byteseq>> Sign(ECDSAParams x, byteseq sk, byteseq msg) {
            try {
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                }
                else {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                }
                ECDomainParameters dp = new ECDomainParameters(p.Curve, p.G, p.N, p.H);
                ECPrivateKeyParameters skp = new ECPrivateKeyParameters(new BigInteger(sk.Elements), dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(true, skp);
                BigInteger[] sig = sign.GenerateSignature(msg.Elements);
                byte[] r = sig[0].ToByteArray();
                byte[] s = sig[1].ToByteArray();
                return new STL.Option_Some<_System.Tuple2<byteseq, byteseq>>(new _System.Tuple2<byteseq, byteseq>(new byteseq(r), new byteseq(s)));
            }
            catch {
                return new STL.Option_None<_System.Tuple2<byteseq, byteseq>>();
            }
        }

    }
}
