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
using Org.BouncyCastle.Asn1;

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
                } else { // x is ECDSA__P256
                    p = ECNamedCurveTable.GetByName("secp256r1");
                    g.Init(new ECKeyGenerationParameters(new ECDomainParameters(p.Curve, p.G, p.N, p.H), rng));
                }
                AsymmetricCipherKeyPair kp = g.GenerateKeyPair();
                ECPoint pt = ((ECPublicKeyParameters)kp.Public).Q;
                // serialize the public and private keys, and then return them
                var vk = SerializeECPoint(pt);
                var sk = byteseq.FromArray(((ECPrivateKeyParameters)kp.Private).D.ToByteArray());
                return new STL.Option_Some<_System.Tuple2<byteseq, byteseq>>(new _System.Tuple2<byteseq, byteseq>(vk, sk));
            } catch {
                return new STL.Option_None<_System.Tuple2<byteseq, byteseq>>();
            }
        }


        /// <summary>
        /// Compresses and encodes an elliptic curve point as described in SEC-1 v2 section 2.3.3,
        /// see http://www.secg.org/sec1-v2.pdf, which says:
        ///     the compressed y-coordinate is placed in the leftmost octet of the octet string
        ///     along with an indication that point compression is on, and the x-coordinate is
        ///     placed in the remainder of the octet string
        /// </summary>
        public static byteseq SerializeECPoint(ECPoint pt) {
            var xBytes = pt.AffineXCoord.GetEncoded();
            var y = pt.AffineYCoord.ToBigInteger();
            byte compressedY = y.Mod(BigInteger.ValueOf(2)).Equals(BigInteger.ValueOf(0)) ? (byte)2 : (byte)3;
            var yBytes = new byte[] { compressedY };
            // return yBytes + xBytes:
            return byteseq.FromArray(yBytes).Concat(byteseq.FromArray(xBytes));
        }

        public static bool Verify(ECDSAParams x, byteseq vk, byteseq digest, byteseq sig) {
            try {
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                } else {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                }
                ECDomainParameters dp = new ECDomainParameters(p.Curve, p.G, p.N, p.H);
                ECPoint pt = p.Curve.DecodePoint(vk.Elements);
                ECPublicKeyParameters vkp = new ECPublicKeyParameters(pt, dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(false, vkp);
                BigInteger r, s;
                DERDeserialize(sig.Elements, out r, out s);
                return sign.VerifySignature(digest.Elements, r, s);
            } catch {
                return false;
            }
        }

        public static STL.Option<byteseq> Sign(ECDSAParams x, byteseq sk, byteseq digest) {
            try {
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                } else {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                }
                ECDomainParameters dp = new ECDomainParameters(p.Curve, p.G, p.N, p.H);
                ECPrivateKeyParameters skp = new ECPrivateKeyParameters(new BigInteger(sk.Elements), dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(true, skp);
                do {
                    BigInteger[] sig = sign.GenerateSignature(digest.Elements);
                    byte[] bytes = DERSerialize(sig[0], sig[1]);
                    if (bytes.Length != x.SignatureLength()) {
                        // Most of the time, a signature of the wrong length can be fixed
                        // by negating s in the signature relative to the group order.
                        bytes = DERSerialize(sig[0], p.N.Subtract(sig[1]));
                    }
                    if (bytes.Length == x.SignatureLength()) {
                        // This will meet the method postcondition, which says that a Some? return must
                        // contain a sequence of bytes whose length is x.SignatureLength().
                        return new STL.Option_Some<byteseq>(byteseq.FromArray(bytes));
                    }
                    // We only get here with low probability, so try again (forever, if we have really bad luck).
                } while (true);
            } catch {
                return new STL.Option_None<byteseq>();
            }
        }

        public static byteseq Digest(ECDSAParams x, byteseq msg) {
            System.Security.Cryptography.HashAlgorithm alg;
            if (x.is_ECDSA__P384) {
                alg = System.Security.Cryptography.SHA384.Create();
            } else {
                alg = System.Security.Cryptography.SHA256.Create();
            }
            byte[] digest = alg.ComputeHash(msg.Elements);
            return byteseq.FromArray(digest);
        }

        private static byte[] DERSerialize(BigInteger r, BigInteger s) {
            DerSequence derSeq = new DerSequence(new DerInteger(r), new DerInteger(s));
            return derSeq.GetEncoded();
        }

        private static void DERDeserialize(byte[] bytes, out BigInteger r, out BigInteger s) {
            Asn1InputStream asn1 = new Asn1InputStream(bytes);
            var seq = (Asn1Sequence)asn1.ReadObject();
            var dr = (DerInteger)seq[0];
            var ds = (DerInteger)seq[1];
            r = new BigInteger(dr.ToString());
            s = new BigInteger(ds.ToString());
        }
    }
}
