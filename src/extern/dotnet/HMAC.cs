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
                // lstCopy should not be mutated, but this is safer than using ps.key.Elements directly
                byte[] lstCopy = new byte[ps.key.Count];
                System.Array.Copy(ps.key.Elements, lstCopy, ps.key.Count);
                var keyParams = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(lstCopy);
                hmac.Init(keyParams);
            }
        }

        public void Update(byte input) {
            hmac.Update(input);
        }

        public void BlockUpdate(byteseq input , int inOff, int len) {
            // lstCopy should not be mutated, but this is safer than using input.Elements directly
            byte[] lstCopy = new byte[input.Count];
            System.Array.Copy(input.Elements, lstCopy, input.Count);
            hmac.BlockUpdate(lstCopy, inOff, len);
        }

        public byteseq DoFinal(byteseq output, int outOff) {
            // lstCopy is mutated here; This prevents unintended mutations to output
            byte[] lstCopy = new byte[output.Count];
            System.Array.Copy(output.Elements, lstCopy, output.Count);
            hmac.DoFinal(lstCopy, outOff);
            return byteseq.FromArray(lstCopy);
        }
    }
}
