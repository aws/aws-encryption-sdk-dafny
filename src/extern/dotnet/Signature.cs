using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Digests;
using Org.BouncyCastle.Crypto.EC;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Encodings;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Prng;
using Org.BouncyCastle.Crypto.Signers;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Math.EC;
using Org.BouncyCastle.OpenSsl;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Asn1.X9;

using byteseq = Dafny.Sequence<byte>;

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
