using System;

using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Signers;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Math.EC;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Asn1.X9;
using Org.BouncyCastle.Asn1;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;

namespace Digest {
    public class DigestUnsupportedException : Exception
    {
        public DigestUnsupportedException(Algorithm alg)
            : base(String.Format("Unsupported digest parameter: {0}", alg))
        {
        }
    }

    public partial class SHA {
        public static STL.Result<ibyteseq> Digest(Algorithm alg, ibyteseq msg) {
            try {
                System.Security.Cryptography.HashAlgorithm hashAlgorithm;
                if (alg.is_SHA__512) {
                    hashAlgorithm = System.Security.Cryptography.SHA512.Create();
                } else {
                    throw new DigestUnsupportedException(alg);
                }
                byte[] digest = hashAlgorithm.ComputeHash(msg.Elements);
                return STL.Result<ibyteseq>.create_Success(byteseq.FromArray(digest));
            } catch (Exception e) {
                return STL.Result<ibyteseq>.create_Failure(Dafny.Sequence<char>.FromString(e.ToString()));
            }
        }
    }
}
