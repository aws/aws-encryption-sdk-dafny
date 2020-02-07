using System;
using System.Numerics;

namespace HMAC {

    public class UnsupportedKeyDerivationAlgorithException : Exception
    {
        public UnsupportedKeyDerivationAlgorithException(Digests.KEY_DERIVATION_ALGORITHM algorithm)
            : base(String.Format("Invalid Key Derivation Algorithm: {0}", algorithm.ToString()))
        {
        }
    }

    public partial class HMac {

        private Org.BouncyCastle.Crypto.Macs.HMac hmac;

        public HMac(Digests.KEY_DERIVATION_ALGORITHM algorithm) {
            Org.BouncyCastle.Crypto.IDigest digest;
            if(algorithm.is_HKDF__WITH__SHA__256) {
                digest = new Org.BouncyCastle.Crypto.Digests.Sha256Digest();
            } else if(algorithm.is_HKDF__WITH__SHA__384) {
                digest = new Org.BouncyCastle.Crypto.Digests.Sha384Digest();
            } else {
                throw new UnsupportedKeyDerivationAlgorithException(algorithm);
            }
            hmac = new Org.BouncyCastle.Crypto.Macs.HMac(digest);
        }

        public Dafny.Sequence<char> GetAlgorithmName() {
            return Dafny.Sequence<char>.FromString(hmac.AlgorithmName);
        }

        public BigInteger GetMacSize() {
            return new BigInteger(hmac.GetMacSize());
        }

        public void Init(CipherParameters ps) {
            if(ps.is_KeyParameter) {
                var keyParams = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(ps.key);
                hmac.Init(keyParams);
            }
        }

        public void Reset() {
            hmac.Reset();
        }

        public void Update(byte input) {
            hmac.Update(input);
        }

        public void BlockUpdate(byte[] input , BigInteger inOff, BigInteger len) {
            hmac.BlockUpdate(input, BigIntegerToInt(inOff), BigIntegerToInt(len));
        }

        public BigInteger DoFinal(byte[] output, BigInteger outOff) {
            return new BigInteger(hmac.DoFinal(output, BigIntegerToInt(outOff)));
        }

        public Org.BouncyCastle.Crypto.IDigest GetUnderlyingDigest() {
            return hmac.GetUnderlyingDigest();
        }

        private int BigIntegerToInt(BigInteger x) {
            // TODO: Error handling?
            return (int) x;
        }
    }
}
