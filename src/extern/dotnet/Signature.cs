using System;

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

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;

namespace Signature {
    public class ECDSAUnsupportedParametersException : Exception
    {
        public ECDSAUnsupportedParametersException(ECDSAParams parameters)
            : base(String.Format("Unsupported ECDSA parameters: {0}", parameters))
        {
        }
    }

    public partial class ECDSA {
        public static STL.Result<SignatureKeyPair> ExternKeyGen(ECDSAParams x) {
            try {
                ECKeyPairGenerator generator = new ECKeyPairGenerator();
                SecureRandom rng = new SecureRandom();
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                } else if (x.is_ECDSA__P256) {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                } else {
                    throw new ECDSAUnsupportedParametersException(x);
                }
                generator.Init(new ECKeyGenerationParameters(new ECDomainParameters(p.Curve, p.G, p.N, p.H), rng));
                AsymmetricCipherKeyPair kp = generator.GenerateKeyPair();
                ECPoint pt = ((ECPublicKeyParameters)kp.Public).Q;
                // serialize the public and private keys, and then return them
                var vk = SerializePublicKey((ECPublicKeyParameters)kp.Public);
                var sk = byteseq.FromArray(((ECPrivateKeyParameters)kp.Private).D.ToByteArray());
                return STL.Result<SignatureKeyPair>.create_Success(new SignatureKeyPair(vk, sk));
            } catch (Exception e) {
                return STL.Result<SignatureKeyPair>.create_Failure(Dafny.Sequence<char>.FromString(e.ToString()));
            }
        }

        /// <summary>
        /// Compresses and encodes the elliptic curve point corresponding to the given public key.
        /// See SEC-1 v2 (http://www.secg.org/sec1-v2.pdf), sections 2.3.3 and 2.3.5. For
        /// example, note:
        ///     the compressed y-coordinate is placed in the leftmost octet of the octet string
        ///     along with an indication that point compression is on, and the x-coordinate is
        ///     placed in the remainder of the octet string
        /// Requires: keyParams.Parameters.Curve is a prime curve (if not, a cast exception will be thrown)
        /// </summary>
        public static ibyteseq SerializePublicKey(ECPublicKeyParameters keyParams) {
            ECPoint pt = keyParams.Q;

            // zero-pad x coordinate
            var xBytes = pt.AffineXCoord.GetEncoded();
            var curve = (FpCurve)keyParams.Parameters.Curve;
            int fieldByteSize = (curve.FieldSize + 7) / 8;
            if (xBytes.Length < fieldByteSize) {
                var paddingLength = fieldByteSize - xBytes.Length;
                var paddedX = new byte[fieldByteSize];
                System.Array.Clear(paddedX, 0, paddingLength);
                xBytes.CopyTo(paddedX, paddingLength);
                xBytes = paddedX;
            }

            // compress y coordinate
            var y = pt.AffineYCoord.ToBigInteger();
            byte compressedY = y.Mod(BigInteger.ValueOf(2)).Equals(BigInteger.ValueOf(0)) ? (byte)2 : (byte)3;
            var yBytes = new byte[] { compressedY };

            // return yBytes + xBytes:
            return byteseq.Concat(byteseq.FromArray(yBytes), (byteseq.FromArray(xBytes)));
        }

        public static STL.Result<bool> Verify(ECDSAParams x, ibyteseq vk, ibyteseq digest, ibyteseq sig) {
            try {
                X9ECParameters parameters;
                if (x.is_ECDSA__P384) {
                    parameters = ECNamedCurveTable.GetByName("secp384r1");
                } else if (x.is_ECDSA__P256) {
                    parameters = ECNamedCurveTable.GetByName("secp256r1");
                } else {
                    throw new ECDSAUnsupportedParametersException(x);
                }
                ECDomainParameters dp = new ECDomainParameters(parameters.Curve, parameters.G, parameters.N, parameters.H);
                ECPoint pt = parameters.Curve.DecodePoint((byte[])vk.Elements.Clone());
                ECPublicKeyParameters vkp = new ECPublicKeyParameters(pt, dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(false, vkp);
                BigInteger r, s;
                DERDeserialize(sig.Elements, out r, out s);
                return STL.Result<bool>.create_Success(sign.VerifySignature(digest.Elements, r, s));
            } catch (Exception e) {
                return STL.Result<bool>.create_Failure(Dafny.Sequence<char>.FromString(e.ToString()));
            }
        }

        public static STL.Result<ibyteseq> Sign(ECDSAParams x, ibyteseq sk, ibyteseq digest) {
            try {
                X9ECParameters p;
                if (x.is_ECDSA__P384) {
                    p = ECNamedCurveTable.GetByName("secp384r1");
                } else if (x.is_ECDSA__P256) {
                    p = ECNamedCurveTable.GetByName("secp256r1");
                } else {
                    throw new ECDSAUnsupportedParametersException(x);
                }
                ECDomainParameters dp = new ECDomainParameters(p.Curve, p.G, p.N, p.H);
                ECPrivateKeyParameters skp = new ECPrivateKeyParameters(new BigInteger(sk.Elements), dp);
                ECDsaSigner sign = new ECDsaSigner();
                sign.Init(true, skp);
                byte[] serializedSignature;
                // This loop can in theory run forever, but the chances of that are negligible.
                // We may want to consider failing, after some number of loops, if we can do so in a way consistent with other ESDKs.
                do {
                    // sig is array of two integers: r and s
                    BigInteger[] sig = sign.GenerateSignature((byte[])digest.Elements.Clone());
                    serializedSignature = DERSerialize(sig[0], sig[1]);
                    if (serializedSignature.Length != x.SignatureLength()) {
                        // Most of the time, a signature of the wrong length can be fixed
                        // by negating s in the signature relative to the group order.
                        serializedSignature = DERSerialize(sig[0], p.N.Subtract(sig[1]));
                    }
                } while (serializedSignature.Length != x.SignatureLength());
                return STL.Result<ibyteseq>.create_Success(byteseq.FromArray(serializedSignature));
            } catch (Exception e) {
                return STL.Result<ibyteseq>.create_Failure(Dafny.Sequence<char>.FromString(e.ToString()));
            }
        }

        public static STL.Result<ibyteseq> Digest(ECDSAParams x, ibyteseq msg) {
            try {
                System.Security.Cryptography.HashAlgorithm alg;
                if (x.is_ECDSA__P384) {
                    alg = System.Security.Cryptography.SHA384.Create();
                } else if (x.is_ECDSA__P256) {
                    alg = System.Security.Cryptography.SHA256.Create();
                } else {
                    throw new ECDSAUnsupportedParametersException(x);
                }
                byte[] digest = alg.ComputeHash(msg.Elements);
                return STL.Result<ibyteseq>.create_Success(byteseq.FromArray(digest));
            } catch (Exception e) {
                return STL.Result<ibyteseq>.create_Failure(Dafny.Sequence<char>.FromString(e.ToString()));
            }
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
