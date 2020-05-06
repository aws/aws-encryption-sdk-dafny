using System;

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
                return DafnyFFI.CreateFailure<ibyteseq>(e.ToString());
            }
        }
    }
}
