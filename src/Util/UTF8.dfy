include "../StandardLibrary/StandardLibrary.dfy"

// Provides a function ValidUTF8 which checks if an array of bytes is a valid sequence of UTF8 code points.
// Each code point of a UTF8 string is one of the following variants, ranging from one to four bytes:
// Case 1 : 0xxxxxxx
// Case 2 : 110xxxxx 10xxxxxx
// Case 3 : 1110xxxx 10xxxxxx 10xxxxxx
// Case 4 : 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx

// The first uint8 of each code point is called the leading uint8, while the rest are called continuation bytes.

// This does NOT perform any range checks on the values encoded.

module {:extern "UTF8"} UTF8 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  type ValidUTF8Bytes = i: seq<uint8> | ValidUTF8Seq(i) witness []

  method {:extern "Encode"} Encode(s: string) returns (res: Result<ValidUTF8Bytes>)
    // US-ASCII only needs a single UTF-8 byte per character
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|

  method {:extern "Decode"} Decode(b: ValidUTF8Bytes) returns (res: Result<string>)

  predicate method IsASCIIString(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] as int < 128
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
  {
    // Based on syntax detailed on https://tools.ietf.org/html/rfc3629#section-4
    0x00 <= s[0] <= 0x7F
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
  {
    // Based on syntax detailed on https://tools.ietf.org/html/rfc3629#section-4
    (0xC2 <= s[0] <= 0xDF) && (0x80 <= s[1] <= 0xBF)
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
  {
    // Based on syntax detailed on https://tools.ietf.org/html/rfc3629#section-4
    ((s[0] == 0xE0) && (0xA0 <= s[1] <= 0xBF) && (0x80 <= s[2] <= 0xBF))
      || ((0xE1 <= s[0] <= 0xEC) && (0x80 <= s[1] <= 0xBF) && (0x80 <= s[2] <= 0xBF))
      || ((s[0] == 0xED) && (0x80 <= s[1] <= 0x9F) && (0x80 <= s[2] <= 0xBF))
      || ((0xEE <= s[0] <= 0xEF) && (0x80 <= s[1] <= 0xBF) && (0x80 <= s[2] <= 0xBF))
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
  {
    // Based on syntax detailed on https://tools.ietf.org/html/rfc3629#section-4
    ((s[0] == 0xF0) && (0x90 <= s[1] <= 0xBF) && (0x80 <= s[2] <= 0xBF) && (0x80 <= s[3] <= 0xBF))
      || ((0xF1 <= s[0] <= 0xF3) && (0x80 <= s[1] <= 0xBF) && (0x80 <= s[2] <= 0xBF) && (0x80 <= s[3] <= 0xBF))
      || ((s[0] == 0xF4) && (0x80 <= s[1] <= 0x8F) && (0x80 <= s[2] <= 0xBF) && (0x80 <= s[3] <= 0xBF))
  }

  predicate method ValidUTF8_at(a: seq<uint8>, offset: nat)
    requires offset <= |a|
    decreases |a| - offset
  {
    var remaining := |a| - offset;
    if remaining == 0 then
      true
    else
      if Uses1Byte(a[offset..]) then
        ValidUTF8_at(a, offset + 1)
      else if remaining >= 2 && Uses2Bytes(a[offset..]) then
        ValidUTF8_at(a, offset + 2)
      else if remaining >= 3 && Uses3Bytes(a[offset..]) then
        ValidUTF8_at(a, offset + 3)
      else if remaining >= 4 && Uses4Bytes(a[offset..]) then
        ValidUTF8_at(a, offset + 4)
      else
        false
  }

  predicate method ValidUTF8Seq(s: seq<uint8>) {
    ValidUTF8_at(s, 0)
  }
}
