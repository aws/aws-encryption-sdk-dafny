// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Security.Cryptography;

using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;

namespace ExternRandom {
    public partial class __default {
        public static Wrappers_Compile._IResult<ibyteseq, icharseq> GenerateBytes(int i) {
            try {
                //= compliance/data-format/message-header.txt#2.5.1.6
                //# While
                //# implementations cannot guarantee complete uniqueness, implementations
                //# MUST use a good source of randomness when generating messages IDs in
                //# order to make the chance of duplicate IDs negligible.
                RandomNumberGenerator rng = RandomNumberGenerator.Create();
                byte[] z = new byte[i];
                rng.GetBytes(z);
                return Wrappers_Compile.Result<ibyteseq, icharseq>.create_Success(Dafny.Sequence<byte>.FromArray(z));
            } catch (Exception e) {
                return DafnyFFI.CreateFailure<ibyteseq>(e.ToString());
            }
        }
    }
}
