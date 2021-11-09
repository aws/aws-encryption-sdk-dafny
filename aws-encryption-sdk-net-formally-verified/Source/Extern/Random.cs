// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Security.Cryptography;

using icharseq = Dafny.ISequence<char>;
using ibyteseq = Dafny.ISequence<byte>;

namespace ExternRandom {
    public partial class __default {
        public static Wrappers_Compile.Result<ibyteseq, icharseq> GenerateBytes(int i) {
            try {
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
