using System;
using System.Text;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace UTF8 {
    public partial class __default {
        public static STL.Result<ibyteseq> Encode(icharseq str) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                byte[] utf8Bytes = utf8.GetBytes(str.Elements);
                return STL.Result<ibyteseq>.create_Success(byteseq.FromArray(utf8Bytes));
            } catch(EncoderFallbackException e) {
                return DafnyFFI.CreateFailure<ibyteseq>( "Input contains invalid Unicode characters");
            } catch(ArgumentNullException e) {
                return DafnyFFI.CreateFailure<ibyteseq>("Input is null");
            }
        }

        public static STL.Result<icharseq> Decode(ibyteseq bytes) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                string decoded = utf8.GetString(bytes.Elements);
                return STL.Result<icharseq>.create_Success(charseq.FromString(decoded));
            } catch(ArgumentException e) {
                // GetString is defined as returning ArgumentException, ArgumentNullException, DecoderFallbackException
                // Both ArgumentNullException and DecoderFallbackException are children of ArgumentException
                return DafnyFFI.CreateFailure<icharseq>("Input contains an invalid Unicode code point");
            }
        }
    }
}
