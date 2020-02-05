using System;
using System.Text;

using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;

namespace UTF8 {
    public partial class __default {
        public static STL.Result<byteseq> Encode(Dafny.Sequence<char> str) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                byte[] utf8Bytes = utf8.GetBytes(str.Elements);
                return new STL.Result_Success<byteseq>(byteseq.FromArray(utf8Bytes));
            } catch(EncoderFallbackException e) {
                return new STL.Result_Failure<byteseq>(charseq.FromArray(
                    "Input contains invalid Unicode characters".ToCharArray()));
            } catch(ArgumentNullException e) {
                return new STL.Result_Failure<byteseq>(charseq.FromArray("Input is null".ToCharArray()));
            }
        }

        public static STL.Result<Dafny.Sequence<char>> Decode(byteseq bytes) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                string decoded = utf8.GetString(bytes.Elements);
                return new STL.Result_Success<Dafny.Sequence<char>>(charseq.FromArray(decoded.ToCharArray()));
            } catch(ArgumentException e) {
                // GetString is defined as returning ArgumentException, ArgumentNullException, DecoderFallbackException
                // Both ArgumentNullException and DecoderFallbackException are children of ArgumentException
                return new STL.Result_Failure<Dafny.Sequence<char>>(charseq.FromArray(
                    "Input contains an invalid Unicode code point".ToCharArray()));
            }
        }
    }
}
