// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Text;

using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace UTF8 {
    public partial class __default {
        public static _IResult<ibyteseq, icharseq> Encode(icharseq str) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                byte[] utf8Bytes = utf8.GetBytes(str.Elements);
                return Result<ibyteseq, icharseq>.create_Success(byteseq.FromArray(utf8Bytes));
            } catch(EncoderFallbackException e) {
                return Result<ibyteseq, icharseq>
                    .create_Failure(Dafny.Sequence<char>.FromString("Input contains invalid Unicode characters"));
            } catch(ArgumentNullException e) {
                return Result<ibyteseq, icharseq>
                    .create_Failure(Dafny.Sequence<char>.FromString("Input is null"));
            }
        }

        public static _IResult<icharseq, icharseq> Decode(ibyteseq bytes) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                string decoded = utf8.GetString(bytes.Elements);
                return Result<icharseq, icharseq>.create_Success(charseq.FromString(decoded));
            } catch(ArgumentException e) {
                // GetString is defined as returning ArgumentException, ArgumentNullException, DecoderFallbackException
                // Both ArgumentNullException and DecoderFallbackException are children of ArgumentException
                return Result<icharseq, icharseq>
                    .create_Failure(Dafny.Sequence<char>.FromString("Input contains an invalid Unicode code point"));
            }
        }
    }
}
