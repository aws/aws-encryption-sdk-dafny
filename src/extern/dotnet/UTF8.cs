using System;
using System.Text;

using byteseq = Dafny.Sequence<byte>;

namespace UTF8 {
  public partial class __default {
    public static STL.Result<byteseq> Encode(Dafny.Sequence<char> str) {
        UTF8Encoding utf8 = new UTF8Encoding(false, true);
        try {
            byte[] utf8Bytes = utf8.GetBytes(str.Elements);
            return new STL.Result_Success<byteseq>(new byteseq(utf8Bytes));
        } catch(EncoderFallbackException e) {
            return new STL.Result_Failure<byteseq>(new Dafny.Sequence<char>("Input contains invalid Unicode characters".ToCharArray()));
        }
    }

    public static STL.Result<Dafny.Sequence<char>> Decode(byteseq bytes) {
        UTF8Encoding utf8 = new UTF8Encoding(false, true);
        try {
            string decoded = utf8.GetString(bytes.Elements);
            return new STL.Result_Success<Dafny.Sequence<char>>(new Dafny.Sequence<char>(decoded.ToCharArray()));
        } catch(DecoderFallbackException e) {
            return new STL.Result_Failure<Dafny.Sequence<char>>(new Dafny.Sequence<char>("Input contains an invalid Unicode code point".ToCharArray()));
        }
    }
  }
}
