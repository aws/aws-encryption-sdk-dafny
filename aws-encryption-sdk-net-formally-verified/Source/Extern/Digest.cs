// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using AWS.EncryptionSDK;
using Wrappers_Compile;
using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;

namespace ExternDigest {
    public class UnsupportedDigestException : AwsEncryptionSdkBaseException
    {
        public UnsupportedDigestException(CryptoDatatypes_Compile.DigestAlgorithm alg)
            : base(String.Format("Unsupported digest parameter: {0}", alg))
        {
        }

        public UnsupportedDigestException(HMAC.Digests digest)
            : base(String.Format("Unsupported digest: {0}", digest.ToString()))
        {
        }

    }

    public partial class __default {
        public static _IResult<ibyteseq, icharseq> Digest(CryptoDatatypes_Compile._IDigestAlgorithm alg, ibyteseq msg) {
            try {
                System.Security.Cryptography.HashAlgorithm hashAlgorithm;
                if (alg.is_SHA__512) {
                    hashAlgorithm = System.Security.Cryptography.SHA512.Create();
                } else {
                    throw new UnsupportedDigestException((CryptoDatatypes_Compile.DigestAlgorithm)alg);
                }
                byte[] digest = hashAlgorithm.ComputeHash(msg.Elements);
                return Result<ibyteseq, icharseq>.create_Success(byteseq.FromArray(digest));
            } catch (Exception e) {
                return DafnyFFI.CreateFailure<ibyteseq>(e.ToString());
            }
        }
    }
}
