// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Wrappers_Compile;
using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using _IDigestAlgorithm = Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm;
using _IError = Dafny.Aws.Cryptography.Primitives.Types._IError;
using Error_Opaque = Dafny.Aws.Cryptography.Primitives.Types.Error_Opaque;
using Error_AwsCryptographicPrimitivesError = Dafny.Aws.Cryptography.Primitives.Types.Error_AwsCryptographicPrimitivesError;

namespace ExternDigest {
    public partial class __default {
        public static _IResult<ibyteseq, _IError> Digest(_IDigestAlgorithm alg, ibyteseq msg) {
            try {
                System.Security.Cryptography.HashAlgorithm hashAlgorithm;
                if (alg.is_SHA__512) {
                    hashAlgorithm = System.Security.Cryptography.SHA512.Create();
                } else if (alg.is_SHA__384) {
                    hashAlgorithm = System.Security.Cryptography.SHA384.Create();
                } else if (alg.is_SHA__256) {
                    hashAlgorithm = System.Security.Cryptography.SHA256.Create();
                } else if (alg.is_SHA__1) {
                    hashAlgorithm = System.Security.Cryptography.SHA1.Create();
                } else {
                    return Result<ibyteseq, _IError>
                        .create_Failure(new Error_AwsCryptographicPrimitivesError(
                            Dafny.Sequence<char>.FromString("Unsupported Hash Algorithm.")
                        ));
                }
                byte[] digest = hashAlgorithm.ComputeHash(msg.Elements);
                return Result<ibyteseq, _IError>
                    .create_Success(byteseq.FromArray(digest));
            } catch (Exception e) {
                return Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(e));
            }
        }
    }
}
