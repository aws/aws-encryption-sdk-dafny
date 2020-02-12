using System;
using System.Numerics;

using byteseq = Dafny.Sequence<byte>;

namespace HMAC {

    public class UnsupportedKeyDerivationAlgorithException : Exception
    {
        public UnsupportedKeyDerivationAlgorithException(Digests.KeyDerivationAlgorithm algorithm)
            : base(String.Format("Invalid Key Derivation Algorithm: {0}", algorithm.ToString()))
        {
        }
    }

    public partial class HMac {

        private Org.BouncyCastle.Crypto.Macs.HMac hmac;

        public HMac(Digests.KeyDerivationAlgorithm algorithm) {
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
                // KeyParameter/ Init should not mutate ps, but this is safer than using ps.key.Elements directly
                byte[] elemCopy = (byte[]) ps.key.Elements.Clone();
                var keyParams = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(elemCopy);
                hmac.Init(keyParams);
            }
        }

        public void Update(byte input) {
            hmac.Update(input);
        }

        public void BlockUpdate(byteseq input , int inOff, int len) {
            // BlockUpdate should not mutate input, but this is safer than using input.Elements directly
            byte[] elemCopy = (byte[]) input.Elements.Clone();
            hmac.BlockUpdate(elemCopy, inOff, len);
        }

        public byteseq GetResult(int length) {
            byte[] output = new byte[length];
            hmac.DoFinal(output, 0);
            return byteseq.FromArray(output);
        }
    }
}
