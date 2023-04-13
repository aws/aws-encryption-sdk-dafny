// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "StandardLibrary.dfy"
include "UInt.dfy"

/*
 * Note that additional lemmas for this module are in Base64Lemmas.dfy.
 */
module Base64 {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  // The maximum index for Base64 is less than 64 (0x40)
  newtype index = x | 0 <= x < 0x40

  // Encoding to Base64 is represented using 24-bit groups
  newtype uint24 = x | 0 <= x < 0x100_0000

  predicate method IsBase64Char(c: char) {
    // char values can be compared using standard relational operators
    // http://leino.science/papers/krml243.html#sec-char
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  predicate method IsUnpaddedBase64String(s: string) {
    // A Base64 encoded string will use 4 ASCII characters for every 3 bytes of data ==> length is divisible by 4
    |s| % 4 == 0 && forall k :: k in s ==> IsBase64Char(k)
  }

  function method IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
  {
    // Based on the Base64 index table
    if i == 63 then '/'
    else if i == 62 then '+'
    // Dafny 1.9.9 added support for char to int conversion
    // https://github.com/dafny-lang/dafny/releases/tag/v1.9.9
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

  lemma CharToIndexToChar(x: char)
    requires IsBase64Char(x)
    ensures IndexToChar(CharToIndex(x)) == x;
  {}

  lemma IndexToCharToIndex(x: index)
    ensures CharToIndex(IndexToChar(x)) == x
  {}

  function method UInt24ToSeq(x: uint24): (ret: seq<uint8>)
    ensures |ret| == 3
    ensures ret[0] as uint24 * 0x1_0000 + ret[1] as uint24 * 0x100 + ret[2] as uint24 == x
  {
    var b0 := (x / 0x1_0000) as uint8;
    var x0 := x - (b0 as uint24 * 0x1_0000);

    var b1 := (x0 / 0x100) as uint8;
    var b2 := (x0 % 0x100) as uint8;
    [b0, b1, b2]
  }

  function method SeqToUInt24(s: seq<uint8>): (x: uint24)
    requires |s| == 3
    ensures UInt24ToSeq(x) == s
  {
    s[0] as uint24 * 0x1_0000 + s[1] as uint24 * 0x100 + s[2] as uint24
  }

  lemma UInt24ToSeqToUInt24(x: uint24)
    ensures SeqToUInt24(UInt24ToSeq(x)) == x
  {}

  lemma SeqToUInt24ToSeq(s: seq<uint8>)
    requires |s| == 3
    ensures UInt24ToSeq(SeqToUInt24(s)) == s
  {}

  function method UInt24ToIndexSeq(x: uint24): (ret: seq<index>)
    ensures |ret| == 4
    ensures ret[0] as uint24 * 0x4_0000 + ret[1] as uint24 * 0x1000 + ret[2] as uint24 * 0x40 + ret[3] as uint24 == x
  {
    // 0x4_0000 represents 64^3
    var b0 := (x / 0x4_0000) as index;
    var x0 := x - (b0 as uint24 * 0x4_0000);

    // 0x1000 represents 64^2
    var b1 := (x0 / 0x1000) as index;
    var x1 := x0 - (b1 as uint24 * 0x1000);

    // 0x40 represents 64^1
    var b2 := (x1 / 0x40) as index;
    var b3 := (x1 % 0x40) as index;
    [b0, b1, b2, b3]
  }

  function method {:vcs_split_on_every_assert} IndexSeqToUInt24(s: seq<index>): (x: uint24)
    requires |s| == 4
    ensures UInt24ToIndexSeq(x) == s
  {
    s[0] as uint24 * 0x4_0000 + s[1] as uint24 * 0x1000 + s[2] as uint24 * 0x40 + s[3] as uint24
  }

  lemma UInt24ToIndexSeqToUInt24(x: uint24)
    ensures IndexSeqToUInt24(UInt24ToIndexSeq(x)) == x
  {}

  lemma IndexSeqToUInt24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures UInt24ToIndexSeq(IndexSeqToUInt24(s)) == s
  {}

  function method DecodeBlock(s: seq<index>): (ret: seq<uint8>)
    requires |s| == 4
    ensures |ret| == 3
    ensures UInt24ToIndexSeq(SeqToUInt24(ret)) == s
  {
    UInt24ToSeq(IndexSeqToUInt24(s))
  }

  function method EncodeBlock(s: seq<uint8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
    ensures UInt24ToSeq(IndexSeqToUInt24(ret)) == s
    ensures DecodeBlock(ret) == s
  {
    UInt24ToIndexSeq(SeqToUInt24(s))
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
    requires IsUnpaddedBase64String(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method EncodeUnpadded(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeUnpadded(s) == b
    ensures |s| % 4 == 0
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeDecodeUnpadded(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeUnpadded(EncodeUnpadded(b)) == b
  {}

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedBase64String(s)
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
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  function method Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
    ensures |s| % 4 == 0
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
    var d := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    // Padding with 2 = implies the sequence represents 1 bytes
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
    ensures |s| % 4 == 0
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
      (IsUnpaddedBase64String(s) ||
      (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
  {
    if s == [] then [] else
      var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
      if Is1Padding(suffix) then
        DecodeUnpadded(prefix) + Decode1Padding(suffix)
      else if Is2Padding(suffix) then
        DecodeUnpadded(prefix) + Decode2Padding(suffix)
      else
        DecodeUnpadded(s)
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<uint8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
      && (Is1Padding(suffix) ==> |b| % 3 == 2)
      && (Is2Padding(suffix) ==> |b| % 3 == 1)
      && (!Is1Padding(suffix) && !Is2Padding(suffix) ==> |b| % 3 == 0)
  {
    if 4 <= |s| {
      var finalBlockStart := |s| - 4;
      var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];

      if s == [] {
      } else if Is1Padding(suffix) {
        assert !Is2Padding(suffix);
        var x, y := DecodeUnpadded(prefix), Decode1Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 2;
        Mod3(|x| / 3, |y|, |b|);
      } else if Is2Padding(suffix) {
        var x, y := DecodeUnpadded(prefix), Decode2Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 1;
        Mod3(|x| / 3, |y|, |b|);
      } else {
        assert b == DecodeUnpadded(s);
      }
    }
  }

  lemma Mod3(x: nat, k: nat, n: nat)
    requires 0 <= k < 3 && n == 3 * x + k
    ensures n % 3 == k
  {
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>, string>)
    ensures IsBase64String(s) ==> b.Success?
    ensures !IsBase64String(s) ==> b.Failure?
  {
    if IsBase64String(s) then Success(DecodeValid(s)) else Failure("The encoding is malformed")
  }

  predicate StringIs7Bit(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] < 128 as char
  }

  lemma ConcatMod4Sequences<T>(s: seq<T>, t: seq<T>)
    requires |s| % 4 == 0;
    requires |t| % 4 == 0;
    ensures |s + t| % 4 == 0;
  {
  }

  function method Encode(b: seq<uint8>): (s: seq<char>)
    ensures StringIs7Bit(s)
    ensures |s| % 4 == 0
    ensures IsBase64String(s)
    // Rather than ensure Decode(s) == Success(b) directly, lemmas are used to verify this property
  {
    if |b| % 3 == 0 then
      var s := EncodeUnpadded(b);
      assert |s| % 4 == 0;
      s
    else if |b| % 3 == 1 then
      assert |b| >= 1;
      var s1, s2 := EncodeUnpadded(b[..(|b| - 1)]), Encode2Padding(b[(|b| - 1)..]);
      ConcatMod4Sequences(s1, s2);
      var s := s1 + s2;
      assert |s| % 4 == 0;
      s
    else
      assert |b| % 3 == 2;
      assert |b| >= 2;
      var s1, s2 := EncodeUnpadded(b[..(|b| - 2)]), Encode1Padding(b[(|b| - 2)..]);
      ConcatMod4Sequences(s1, s2);
      var s := s1 + s2;
      assert |s| % 4 == 0;
      s
  }

  lemma EncodeLengthExact(b: seq<uint8>)
    ensures var s := Encode(b);
      && (|b| % 3 == 0 ==> |s| == |b| / 3 * 4)
      && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
  {
    var s := Encode(b);
    if |b| % 3 == 0 {
      assert s == EncodeUnpadded(b);
      assert |s| == |b| / 3 * 4;
    } else if |b| % 3 == 1 {
      assert s == EncodeUnpadded(b[..(|b| - 1)]) + Encode2Padding(b[(|b| - 1)..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..(|b| - 1)])| + |Encode2Padding(b[(|b| - 1)..])|;
      ==  { assert |Encode2Padding(b[(|b| - 1)..])| == 4; }
        |EncodeUnpadded(b[..(|b| - 1)])| + 4;
      ==  { assert |EncodeUnpadded(b[..(|b| - 1)])| == |b[..(|b| - 1)]| / 3 * 4; }
        |b[..(|b| - 1)]| / 3 * 4 + 4;
      ==  { assert |b[..(|b| - 1)]| == |b| - 1; }
        (|b| - 1) / 3 * 4 + 4;
      ==  { assert (|b| - 1) / 3 == |b| / 3; }
        |b| / 3 * 4 + 4;
      }
    } else {
      assert s == EncodeUnpadded(b[..(|b| - 2)]) + Encode1Padding(b[(|b| - 2)..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..(|b| - 2)])| + |Encode1Padding(b[(|b| - 2)..])|;
      ==  { assert |Encode1Padding(b[(|b| - 2)..])| == 4; }
        |EncodeUnpadded(b[..(|b| - 2)])| + 4;
      ==  { assert |EncodeUnpadded(b[..(|b| - 2)])| == |b[..(|b| - 2)]| / 3 * 4; }
        |b[..(|b| - 2)]| / 3 * 4 + 4;
      ==  { assert |b[..(|b| - 2)]| == |b| - 2; }
        (|b| - 2) / 3 * 4 + 4;
      ==  { assert (|b| - 2) / 3 == |b| / 3; }
        |b| / 3 * 4 + 4;
      }
      assert (var s := Encode(b);
              && (|b| % 3 == 0 ==> |s| == |b| / 3 * 4)
              && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4));
    }
  }

  lemma EncodeLengthBound(b: seq<uint8>)
    ensures var s := Encode(b);
      |s| <= |b| / 3 * 4 + 4
  {
    EncodeLengthExact(b);
  }
}
