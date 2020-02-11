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

        public void Init(CipherParameters ps) {
            if(ps.is_KeyParameter) {
                var keyParams = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(ps.key.Elements);
                hmac.Init(keyParams);
            }
        }

        public void Update(byte input) {
            hmac.Update(input);
        }

        public void BlockUpdate(byteseq input , int inOff, int len) {
            hmac.BlockUpdate(input.Elements, inOff, len);
        }

        public byteseq DoFinal(byteseq output, int outOff) {
            byte[] lstCopy = new byte[output.Elements.Length];
            System.Array.Copy(output.Elements, lstCopy, output.Elements.Length);
            hmac.DoFinal(lstCopy, outOff);
            return byteseq.FromArray(lstCopy);
        }
    }
}
