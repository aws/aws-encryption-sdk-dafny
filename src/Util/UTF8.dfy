// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  type ValidUTF8Bytes = i: seq<uint8> | ValidUTF8Seq(i) witness []

  // The tradeoff of assuming the external implementation of encode and decode is correct is worth the tradeoff
  // of unlocking being able to express and hence prove so many other specifications
  function method {:extern "Encode"} Encode(s: string): (res: Result<ValidUTF8Bytes, string>)
    // US-ASCII only needs a single UTF-8 byte per character
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|

  // Decode return a Result, therefore doesn't need to require utf8 input
  function method {:extern "Decode"} Decode(b: seq<uint8>): (res: Result<string, string>)
    ensures res.Success? ==> ValidUTF8Seq(b)

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

  predicate method {:tailrecursion} ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r := a[lo..hi];
      if Uses1Byte(r) then
        ValidUTF8Range(a, lo + 1, hi)
      else if 2 <= |r| && Uses2Bytes(r) then
        ValidUTF8Range(a, lo + 2, hi)
      else if 3 <= |r| && Uses3Bytes(r) then
        ValidUTF8Range(a, lo + 3, hi)
      else if 4 <= |r| && Uses4Bytes(r) then
        ValidUTF8Range(a, lo + 4, hi)
      else
        false
  }

  lemma ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
    if lo == hi {
    } else {
      var r := b[lo..hi];
      var r' := (a + b + c)[|a| + lo..|a| + hi];
      assert r == r';
      if Uses1Byte(r) {
        ValidUTF8Embed(a, b, c, lo + 1, hi);
      } else if 2 <= |r| && Uses2Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 2, hi);
      } else if 3 <= |r| && Uses3Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 3, hi);
      } else if 4 <= |r| && Uses4Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 4, hi);
      }
    }
  }

  predicate method ValidUTF8Seq(s: seq<uint8>) {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
  {
    var lo := 0;
    while lo < |s|
      invariant lo <= |s|
      invariant ValidUTF8Range(s, lo, |s|)
      invariant ValidUTF8Range(s + t, 0, |s + t|) == ValidUTF8Range(s + t, lo, |s + t|)
    {
      var r := (s + t)[lo..];
      if Uses1Byte(r) {
        lo := lo + 1;
      } else if 2 <= |r| && Uses2Bytes(r) {
        lo := lo + 2;
      } else if 3 <= |r| && Uses3Bytes(r) {
        lo := lo + 3;
      } else if 4 <= |r| && Uses4Bytes(r) {
        lo := lo + 4;
      }
    }
    calc {
      ValidUTF8Seq(s + t);
    ==  // def.ValidUTF8Seq
      ValidUTF8Range(s + t, 0, |s + t|);
    ==  // loop invariant
      ValidUTF8Range(s + t, lo, |s + t|);
    ==  { assert s + t == s + t + [] && lo == |s| && |s + t| == |s| + |t|; }
      ValidUTF8Range(s + t + [], |s|, |s| + |t|);
    ==  { ValidUTF8Embed(s, t, [], 0, |t|); }
      ValidUTF8Range(t, 0, |t|);
    ==  // def.ValidUTF8Seq
      ValidUTF8Seq(t);
    ==  // precondition
      true;
    }
  }
}
