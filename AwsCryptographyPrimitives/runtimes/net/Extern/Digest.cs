// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Wrappers_Compile;
using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using _IDigestAlgorithm = software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm;
using _IError = software.amazon.cryptography.primitives.internaldafny.types._IError;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;
using Error_AwsCryptographicPrimitivesError = software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError;

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
                    .create_Failure(AWS.Cryptography.Primitives.TypeConversion.ToDafny_CommonError(e));
            }
        }
    }
}
