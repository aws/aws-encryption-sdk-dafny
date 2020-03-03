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
                return STL.Result<byteseq>.create_Success(byteseq.FromArray(utf8Bytes));
            } catch(EncoderFallbackException e) {
                return STL.Result<byteseq>.create_Failure(charseq.FromArray(
                    "Input contains invalid Unicode characters".ToCharArray()));
            } catch(ArgumentNullException e) {
                return STL.Result<byteseq>.create_Failure(charseq.FromArray("Input is null".ToCharArray()));
            }
        }

        public static STL.Result<Dafny.Sequence<char>> Decode(byteseq bytes) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            try {
                string decoded = utf8.GetString(bytes.Elements);
                return STL.Result<charseq>.create_Success(charseq.FromString(decoded));
            } catch(ArgumentException e) {
                // GetString is defined as returning ArgumentException, ArgumentNullException, DecoderFallbackException
                // Both ArgumentNullException and DecoderFallbackException are children of ArgumentException
                return STL.Result<Dafny.Sequence<char>>.create_Failure(charseq.FromArray(
                    "Input contains an invalid Unicode code point".ToCharArray()));
            }
        }
    }
}
