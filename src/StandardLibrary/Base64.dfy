include "StandardLibrary.dfy"
include "UInt.dfy"

module Base64 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // The maximum index for Base64 is less than 64 (0x40)
  newtype index = x | 0 <= x < 0x40

  newtype base64 = x | 0 <= x < 0x100_0000

  predicate method IsBase64Char(c: char) {
    var i := c as int;
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  predicate method IsUnpaddedString(s: string) {
    // A Base64 encoded string will use 4 ASCII characters for every 3 bytes of data ==> length is divisible by 4
    |s| % 4 == 0 && forall k :: k in s ==> IsBase64Char(k)
  }

  function method IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
  {
    // Based on the Base64 index table
    if i == 63 then '/'
    else if i == 62 then '+'
    // 0 - 9
    else if 52 <= i <= 61 then (i - 4) as char
    // a - z
    else if 26 <= i <= 51 then i as char + 71 as char
    // A - Z
    else i as char + 65 as char
  }

  function method CharToIndex(c: char): (i: index)
    requires IsBase64Char(c)
    ensures IndexToChar(i) == c
  {
    // Perform the inverse operations of IndexToChar
    if c == '/' then 63
    else if c == '+' then 62
    else if '0' <= c <= '9' then (c + 4 as char) as index
    else if 'a' <= c <= 'z' then (c - 71 as char) as index
    else (c - 65 as char) as index
  }

  function method Base64ToSeq(x: base64): (ret: seq<uint8>)
    ensures |ret| == 3
    ensures ret[0] as base64 * 0x1_0000 + ret[1] as base64 * 0x100 + ret[2] as base64 == x
  {
    var b0 := (x / 0x1_0000) as uint8;
    var x0 := x - (b0 as base64 * 0x1_0000);

    var b1 := (x0 / 0x100) as uint8;
    var b2 := (x0 % 0x100) as uint8;
    [b0, b1, b2]
  }

  function method SeqToBase64(s: seq<uint8>): (x: base64)
    requires |s| == 3
    ensures Base64ToSeq(x) == s
  {
    s[0] as base64 * 0x1_0000 + s[1] as base64 * 0x100 + s[2] as base64
  }

  lemma Base64SeqSerializeDeserialize(x: base64)
    ensures SeqToBase64(Base64ToSeq(x)) == x
  {}

  lemma Base64SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 3
    ensures Base64ToSeq(SeqToBase64(s)) == s
  {}

  function method Base64ToIndexSeq(x: base64): (ret: seq<index>)
    ensures |ret| == 4
    ensures ret[0] as base64 * 0x4_0000 + ret[1] as base64 * 0x1000 + ret[2] as base64 * 0x40 + ret[3] as base64 == x
  {
    // 0x4_0000 represents 64^3
    var b0 := (x / 0x4_0000) as index;
    var x0 := x - (b0 as base64 * 0x4_0000);

    // 0x1000 represents 64^2
    var b1 := (x0 / 0x1000) as index;
    var x1 := x0 - (b1 as base64 * 0x1000);

    // 0x40 represents 64^1
    var b2 := (x1 / 0x40) as index;
    var b3 := (x1 % 0x40) as index;
    [b0, b1, b2, b3]
  }

  function method IndexSeqToBase64(s: seq<index>): (x: base64)
    requires |s| == 4
    ensures Base64ToIndexSeq(x) == s
  {
    s[0] as base64 * 0x4_0000 + s[1] as base64 * 0x1000 + s[2] as base64 * 0x40 + s[3] as base64
  }

  lemma IndexSeqSerializeDeserialize(x: base64)
    ensures IndexSeqToBase64(Base64ToIndexSeq(x)) == x
  {}

  lemma IndexSeqDeserializeSerialize(s: seq<index>)
    requires |s| == 4
    ensures Base64ToIndexSeq(IndexSeqToBase64(s)) == s
  {}

  function method DecodeBlock(s: seq<index>): (ret: seq<uint8>)
    requires |s| == 4
    ensures |ret| == 3
    ensures Base64ToIndexSeq(SeqToBase64(ret)) == s
  {
    Base64ToSeq(IndexSeqToBase64(s))
  }

  function method EncodeBlock(s: seq<uint8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
    ensures Base64ToSeq(IndexSeqToBase64(ret)) == s
    ensures DecodeBlock(ret) == s
  {
    Base64ToIndexSeq(SeqToBase64(s))
  }

  lemma EncodeDecodeBlock(s: seq<uint8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
  {}

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
  {}

  function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
    requires |s| % 4 == 0
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    ensures |b| == 0 ==> |s| == 0
    ensures |b| != 0 ==> EncodeBlock(b[..3]) == s[..4]
    decreases |s|
  {
    if |s| == 0 then []
    else DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  }

  function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
    ensures DecodeRecursively(s) == b
  {
    if |b| == 0 then []
    else EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  }
  
  lemma DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures EncodeRecursively(DecodeRecursively(s)) == s
  {}

  lemma EncodeDecodeRecursively(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeRecursively(EncodeRecursively(b)) == b
  {}

  function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
    ensures forall k :: 0 <= k < |b| ==> IndexToChar(b[k]) == s[k]
  {
    seq(|s|, i requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
    ensures forall k :: 0 <= k < |s| ==> CharToIndex(s[k]) == b[k]
    ensures FromCharsToIndices(s) == b
  {
    seq(|b|, i requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
  {}

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
  {}

  function method DecodeUnpadded(s: seq<char>): (b: seq<uint8>)
    requires IsUnpaddedString(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method EncodeUnpadded(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedString(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeUnpadded(s) == b
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeDecodeUnpadded(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeUnpadded(EncodeUnpadded(b)) == b
  {}

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedString(s)
    ensures EncodeUnpadded(DecodeUnpadded(s)) == s
  {
    var fromCharsToIndicesS := FromCharsToIndices(s);
    calc {
      EncodeUnpadded(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeRecursively(FromCharsToIndices(s)));
    ==
      EncodeUnpadded(DecodeRecursively(fromCharsToIndicesS));
    ==
      assert |fromCharsToIndicesS| % 4 == 0;
      assert |DecodeRecursively(fromCharsToIndicesS)| % 3 == 0;
      FromIndicesToChars(EncodeRecursively(DecodeRecursively(fromCharsToIndicesS)));
    == { DecodeEncodeRecursively(fromCharsToIndicesS); }
      FromIndicesToChars(fromCharsToIndicesS);
    ==
      FromIndicesToChars(FromCharsToIndices(s));
    == { FromCharsToIndicesToChars(s); }
      s;
    }
  }

  predicate method Is1Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    // This is a result of the padded 0's in the sextet in the final element before the =
    CharToIndex(s[2]) % 0x4 == 0 &&
    s[3] == '='
  }

  function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
    requires Is1Padding(s)
    // Padding with 1 = implies the sequence represents 2 bytes
    ensures |b| == 2
  {
    // CharToIndex('A') == 0, so 'A' ensures the final element doesn't affect the DecodeBlock conversion for s
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), CharToIndex('A')]);
    [d[0], d[1]]
  }

  function method Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
  {
    // 0 is used to ensure that the final element doesn't affect the EncodeBlock conversion for b
    var e := EncodeBlock([b[0], b[1], 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']
  }

  lemma DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
  {}

  lemma EncodeDecode1Padding(b: seq<uint8>)
    requires |b| == 2
    ensures Decode1Padding(Encode1Padding(b)) == b
  {}

  predicate method Is2Padding(s: seq<char>) {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    // This is a result of the padded 0's in the sextet in the final element before the two =
    CharToIndex(s[1]) % 0x10 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
    requires Is2Padding(s)
    // Padding with 2 = implies the sequence represents 1 byte
    ensures |b| == 1
  {
    // CharToIndex('A') == 0, so 'A' ensures the final two elements don't affect the DecodeBlock conversion for s
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex('A'), CharToIndex('A')]);
    [d[0]]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    // Padding with 2 = implies the sequence represents 1 bytes
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
  {
    // 0 is used to ensure that the final two elements don't affect the EncodeBlock conversion for b
    var e := EncodeBlock([b[0], 0, 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']
  }

  lemma DecodeEncode2Padding(s: seq<char>)
    requires Is2Padding(s)
    ensures Encode2Padding(Decode2Padding(s)) == s
  {}

  lemma EncodeDecode2Padding(b: seq<uint8>)
    requires |b| == 1
    ensures Decode2Padding(Encode2Padding(b)) == b
  {}

  predicate method IsBase64String(s: string) {
    // All Base64 strings are unpadded until the final block of 4 elements, where a padded seq could exist
    var finalBlockStart := |s| - 4;
    (|s| % 4 == 0) &&
      (IsUnpaddedString(s) ||
      (IsUnpaddedString(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
    ensures s == [] ==> b == []
    ensures |s| >= 4 && Is1Padding(s[(|s| - 4)..]) ==> b == (DecodeUnpadded(s[..(|s| - 4)]) + Decode1Padding(s[(|s| - 4)..]))
    ensures |s| >= 4 && Is2Padding(s[(|s| - 4)..]) ==> b == (DecodeUnpadded(s[..(|s| - 4)]) + Decode2Padding(s[(|s| - 4)..]))
    ensures |s| >= 4 && !Is1Padding(s[(|s| - 4)..]) && !Is2Padding(s[(|s| - 4)..]) ==> b == DecodeUnpadded(s)
  {
    var finalBlockStart := |s| - 4;
    if s == [] then []
    else if Is1Padding(s[finalBlockStart..]) then DecodeUnpadded(s[..finalBlockStart]) + Decode1Padding(s[finalBlockStart..])
    else if Is2Padding(s[finalBlockStart..]) then DecodeUnpadded(s[..finalBlockStart]) + Decode2Padding(s[finalBlockStart..])
    else DecodeUnpadded(s)
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>>)
    ensures IsBase64String(s) ==> b.Success? == true
  {
    if IsBase64String(s) then Success(DecodeValid(s)) else Failure("The encoding is malformed")
  }

  predicate StringIs8Bit(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] < 256 as char
  }

  function method Encode(b: seq<uint8>): (s: seq<char>)
    ensures StringIs8Bit(s)
    ensures IsBase64String(s)
    ensures Decode(s) == Success(b)
    ensures |b| % 3 == 0 ==> s == EncodeUnpadded(b)
    ensures |b| % 3 == 1 ==> s == (EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..]))
    ensures |b| % 3 == 2 ==> s == (EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..]))
  {
    var res := (
      if |b| % 3 == 0 then EncodeUnpadded(b)
      else if |b| % 3 == 1 then EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..])
      else EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..])
    );
    assert DecodeValid(res) == b;
    res
  }

  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures Encode(DecodeValid(s)) == s
  {}

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[(|s| - 4)..])
    requires !Is2Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      Encode(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeUnpadded(s));
    == { DecodeEncodeUnpadded(s); }
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[..(|DecodeValid(s)| - 2)] == DecodeUnpadded(s[..(|s| - 4)])
  {}

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[(|DecodeValid(s)| - 2)..] == Decode1Padding(s[(|s| - 4)..])
  {}

  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 2;
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 2)]) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValidUnpaddedPartialFrom1PaddedSeq(s); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode1Padding(DecodeValid(s)[(|DecodeValid(s)| - 2)..]);
    == { DecodeValid1PaddedPartialFrom1PaddedSeq(s); }
      s[..(|s| - 4)] + Encode1Padding(Decode1Padding(s[(|s| - 4)..]));
    == { DecodeEncode1Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    ==
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[..(|DecodeValid(s)| - 1)] == DecodeUnpadded(s[..(|s| - 4)])
  {}

  lemma DecodeValid2PaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures DecodeValid(s)[(|DecodeValid(s)| - 1)..] == Decode2Padding(s[(|s| - 4)..])
  {}

  lemma DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[(|s| - 4)..])
    ensures Encode(DecodeValid(s)) == s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 1;
      EncodeUnpadded(DecodeValid(s)[..(|DecodeValid(s)| - 1)]) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValidUnpaddedPartialFrom2PaddedSeq(s); }
      EncodeUnpadded(DecodeUnpadded(s[..(|s| - 4)])) + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeEncodeUnpadded(s[..(|s| - 4)]); }
      s[..(|s| - 4)] + Encode2Padding(DecodeValid(s)[(|DecodeValid(s)| - 1)..]);
    == { DecodeValid2PaddedPartialFrom2PaddedSeq(s); }
      s[..(|s| - 4)] + Encode2Padding(Decode2Padding(s[(|s| - 4)..]));
    == { DecodeEncode2Padding(s[(|s| - 4)..]); }
      s[..(|s| - 4)] + s[(|s| - 4)..];
    ==
      s;
    }
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(DecodeValid(s)) == s
  {
    if s == [] {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeEmpty(s); }
        s;
      }
    } else if |s| >= 4 && Is1Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode1Padding(s); }
        s;
      }
    } else if |s| >= 4 && Is2Padding(s[(|s| - 4)..]) {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncode2Padding(s); }
        s;
      }
    } else {
      calc {
        Encode(DecodeValid(s));
      == { DecodeValidEncodeUnpadded(s); }
        s;
      }
    }
  }

  lemma EncodeDecodeValid(b: seq<uint8>)
    ensures DecodeValid(Encode(b)) == b
  {}
}
