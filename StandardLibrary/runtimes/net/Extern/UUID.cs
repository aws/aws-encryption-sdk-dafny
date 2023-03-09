// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace UUID {
    public partial class __default {
        public static _IResult<ibyteseq, icharseq> ToByteArray(icharseq s) {
            try {
                Guid fromString = new Guid(new String(s.CloneAsArray()));
                byte[] bytes = ReOrderUuidBytes(fromString.ToByteArray());
                return Result<ibyteseq, icharseq>.create_Success(byteseq.FromArray(bytes));
            } catch (Exception e) when (e is ArgumentNullException or FormatException or OverflowException) {
                return Result<ibyteseq, icharseq>
                    .create_Failure(Dafny.Sequence<char>.FromString("Unable to convert input to a UUID"));
            }
        }
        public static _IResult<icharseq, icharseq> FromByteArray(ibyteseq b) {
            try {
                byte[] bytes = ReOrderUuidBytes(b.CloneAsArray());
                Guid fromBytes = new Guid(bytes);
                return Result<icharseq, icharseq>.create_Success(charseq.FromString(fromBytes.ToString()));
            }
            catch (Exception e) when (e is ArgumentNullException or ArgumentException) {
                return Result<icharseq, icharseq>.create_Failure(
                    charseq.FromString("Unable to convert bytes to valid UUID"));
            }
        }

        public static _IResult<icharseq, icharseq> GenerateUUID() { 
            Guid uuid = Guid.NewGuid();
            return Result<icharseq, icharseq>.create_Success(charseq.FromString(uuid.ToString()));
        }

        // https://learn.microsoft.com/en-us/dotnet/api/system.guid.tobytearray?redirectedfrom=MSDN&view=net-7.0#remarks
        private static byte[] ReOrderUuidBytes(byte[] uuid) {
            // When using the .ToByteArray() method the byte 
            // representation is different than that of the 
            // string representation. 
            // The order of the beginning four-byte group and
            // the next two two-byte groups is reversed
            // whereas the order of the last two-byte group 
            // and the closing six-byte group is the same 
            byte[] bytes = {
                uuid[3],
                uuid[2],
                uuid[1],
                uuid[0],
                uuid[5],
                uuid[4],
                uuid[7],
                uuid[6],
                uuid[8],
                uuid[9],
                uuid[10],
                uuid[11],
                uuid[12],
                uuid[13],
                uuid[14],
                uuid[15]
            };
            return bytes;
        } 
    }
}
