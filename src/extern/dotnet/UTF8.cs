using System;
using System.Text;

using byteseq = Dafny.Sequence<byte>;
using charseq = Dafny.Sequence<char>;

namespace UTF8 {
  public partial class __default {
    public static byteseq Encode(Dafny.Sequence<char> str) {
      UTF8Encoding utf8 = new UTF8Encoding(false, true);
      byte[] utf8Bytes = utf8.GetBytes(str.Elements);
      return byteseq.FromArray(utf8Bytes);
    }

    public static Dafny.Sequence<char> Decode(byteseq bytes) {
      UTF8Encoding utf8 = new UTF8Encoding(false, true);
      string decoded = utf8.GetString(bytes.Elements);
      return charseq.FromArray(decoded.ToCharArray());
    }
  }
}
