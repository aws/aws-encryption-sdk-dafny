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

  function method {:extern "Encode"} Encode(s: string): Result<ValidUTF8Bytes>
    ensures IsASCIIString(s) ==> Encode(s).Success? && |Encode(s).value| == |s|

  // Issue #81
  function method {:extern "Decode"} Decode(s: ValidUTF8Bytes): Result<string>

  predicate IsASCIIString(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] as int < 128
  }

  // Returns the value of the idx'th bit, from least to most significant bit (0- indexed)
  function method BitAt(x: uint8, idx: uint8): bool
    requires idx < 8
  {
    var w := x as bv8;
    (w >> idx) & 1 == 1
  }

  // Checks if a[offset] is a valid continuation uint8.
  predicate method ValidUTF8Continuation(a: seq<uint8>, offset: nat)
    requires offset < |a|
  {
    BitAt(a[offset], 7) && !BitAt(a[offset], 6)
  }

  // Returns which leading uint8 is at a[offset], or 0 if it is not a leading uint8.
  function method CodePointCase(a: seq<uint8>, offset: nat): uint8
    requires offset < |a|
  {
    if BitAt(a[offset], 7) then // 1xxx xxxx
      if BitAt(a[offset], 6) then //11xx xxxx
        if BitAt(a[offset], 5) then // 111x xxxx
          if BitAt(a[offset], 4) then // 1111 xxxx
            if BitAt(a[offset], 3) then // 1111 1xxx
              0 // Error case
            else // 1111 0xxx
              4
          else // 1110 xxxx
            3
        else // 110x xxxx
          2
      else //10xx xxxx
        0 // Error case
    else //0xxxxxxx
      1
  }

  predicate method ValidUTF8_at(a: seq<uint8>, offset: nat)
    requires offset <= |a|
    decreases |a| - offset
  {
    if offset == |a|
    then true
    else
      var c := CodePointCase(a, offset);
      if c == 1 then
        ValidUTF8_at(a, offset + 1)
      else if c == 2 then
        offset + 2 <= |a| &&
        ValidUTF8Continuation(a, offset + 1) &&
        ValidUTF8_at(a, offset + 2)
      else if c == 3 then
        offset + 3 <= |a| &&
        ValidUTF8Continuation(a, offset + 1) &&
        ValidUTF8Continuation(a, offset + 2) &&
        ValidUTF8_at(a, offset + 3)
      else if c == 4 then
        offset + 4 <= |a| &&
        ValidUTF8Continuation(a, offset + 1) &&
        ValidUTF8Continuation(a, offset + 2) &&
        ValidUTF8Continuation(a, offset + 3) &&
        ValidUTF8_at(a, offset + 4)
      else
        false
  }

  predicate method ValidUTF8(a: array<uint8>)
    reads a
  {
    ValidUTF8_at(a[..], 0)
  }

  // Issue #82
  predicate method ValidUTF8Seq(s: seq<uint8>) {
    ValidUTF8_at(s, 0)
  }
}
