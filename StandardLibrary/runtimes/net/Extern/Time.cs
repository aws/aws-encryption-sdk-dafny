// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Numerics;
using Microsoft.VisualBasic;
using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace Time {

    public partial class __default {
        public static long CurrentRelativeTime()
        {
            var timespan = DateTime.Now - DateTime.MinValue;
            return (long) timespan.TotalSeconds;
        }

        public static _IResult<icharseq, icharseq> GetCurrentTimeStamp()
        {
            var utcTime = DateTime.UtcNow;
            try
            {
                // DateTime has format specifiers that make it easy to specify time stamp in different formats
                // using "o" as the format specifier gives us a time stamp in ISO8601
                // https://learn.microsoft.com/en-us/dotnet/standard/base-types/standard-date-and-time-format-strings#Roundtrip
                var timestamp = utcTime.ToString("yyyy'-'MM'-'dd'T'HH':'mm':'ss'.'ffffffK");
                return Result<icharseq, icharseq>.create_Success(charseq.FromString(timestamp));
            }
            catch (Exception e) when (e is ArgumentOutOfRangeException or FormatException)
            {
                return Result<icharseq, icharseq>.create_Failure(
                    charseq.FromString("Unable to generate timestamp in ISO8601 UTC format."));
            }
        }
    }
}
