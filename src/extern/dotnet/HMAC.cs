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

        public int GetMacSize() {
            return hmac.GetMacSize();
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

        public void BlockUpdate(byte[] input , int inOff, int len) {
            hmac.BlockUpdate(input, inOff, len);
        }

        public int DoFinal(byte[] output, int outOff) {
            return hmac.DoFinal(output, outOff);
        }

        public Org.BouncyCastle.Crypto.IDigest GetUnderlyingDigest() {
            return hmac.GetUnderlyingDigest();
        }
    }
}
