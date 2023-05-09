// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Security.Cryptography;

using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using _IError = software.amazon.cryptography.primitives.internaldafny.types._IError;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;

namespace ExternRandom {
    public partial class __default {
        public static Wrappers_Compile._IResult<
            ibyteseq,
            software.amazon.cryptography.primitives.internaldafny.types._IError
        > GenerateBytes(int i) {
            try {
                //= compliance/data-format/message-header.txt#2.5.1.6
                //# While
                //# implementations cannot guarantee complete uniqueness, implementations
                //# MUST use a good source of randomness when generating messages IDs in
                //# order to make the chance of duplicate IDs negligible.
                RandomNumberGenerator rng = RandomNumberGenerator.Create();
                byte[] z = new byte[i];
                rng.GetBytes(z);
                return Wrappers_Compile.Result<ibyteseq, _IError>
                    .create_Success(Dafny.Sequence<byte>.FromArray(z));
            } catch (Exception e) {
                return Wrappers_Compile.Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(e));
            }
        }
    }
}
