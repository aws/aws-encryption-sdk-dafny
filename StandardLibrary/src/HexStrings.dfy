// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "StandardLibrary.dfy"

module HexStrings {
  import opened Wrappers
  import opened StandardLibrary
  import opened StandardLibrary.UInt

  // return the hex character for this hex value
  function method HexChar(x : uint8) : (res : char)
    requires x < 16
    ensures '0' <= res <= '9' || 'a' <= res <= 'f'
    ensures IsHexChar(res)
  {
    if x < 10 then
      '0' + x as char
    else
      'a' + (x - 10) as char
  }

  // either case
  predicate method IsLooseHexChar(ch : char)
  {
    || '0' <= ch <= '9'
    || 'a' <= ch <= 'f'
    || 'A' <= ch <= 'F'
  }

  // lowercase only. RoundTrip lemmas only work on this kind.
  predicate method IsHexChar(ch : char)
  {
    || '0' <= ch <= '9'
    || 'a' <= ch <= 'f'
  }

  lemma PlainIsLooseChar(ch : char)
    requires IsHexChar(ch)
    ensures IsLooseHexChar(ch)
  {}

  lemma PlainIsLooseString(s : string)
    requires IsHexString(s)
    ensures IsLooseHexString(s)
  {}

  predicate method IsHexString(s : string)
  {
    forall ch <- s :: IsHexChar(ch)
  }

  predicate method IsLooseHexString(s : string)
  {
    forall ch <- s :: IsLooseHexChar(ch)
  }

  type HexString = x : string | IsHexString(x)
  type LooseHexString = x : string | IsLooseHexString(x)

  // return the hex value for this hex character
  function method HexVal(ch : char) : (res : uint8)
    requires IsLooseHexChar(ch)
    ensures 0 <= res < 16
  {
    if '0' <= ch <= '9' then
      ch as uint8 - '0' as uint8
    else if 'a' <= ch <= 'f' then
      ch as uint8 - 'a' as uint8 + 10
    else
      assert 'A' <= ch <= 'F';
      ch as uint8 - 'A' as uint8 + 10
  }

  lemma HexCharRoundTrip(ch : char)
    requires IsHexChar(ch)
    ensures HexChar(HexVal(ch)) == ch
  {}

  lemma HexValRoundTrip(x : uint8)
    requires x < 16
    ensures HexVal(HexChar(x)) == x
  {}

  // return the hex string for this byte
  function method HexStr(x : uint8) : (ret : string)
    ensures |ret| == 2
  {
    if x < 16 then
      var res := ['0', HexChar(x)];
      res
    else
      var res := [HexChar((x / 16) as uint8), HexChar((x % 16) as uint8)];
      res
  }

  // return the byte for this hex string
  function method HexValue(x : string) : (ret : uint8)
    requires |x| == 2
    requires IsLooseHexChar(x[0]) && IsLooseHexChar(x[1])
  {
    HexVal(x[0]) * 16 + HexVal(x[1])
  }

  lemma HexValueRoundTrip(x : uint8)
    ensures HexValue(HexStr(x)) == x
  {}
  lemma HexStrRoundTrip(x : string)
    requires |x| == 2
    requires IsHexChar(x[0]) && IsHexChar(x[1])
    ensures HexStr(HexValue(x)) == x
  {}

  // return the hex string for these bytes, keeping any leading zero
  function method {:tailrecursion} ToHexString(val : seq<uint8>) : (ret : HexString)
    ensures |ret| == 2 * |val|
  {
    if |val| == 0 then
      []
    else
      HexStr(val[0]) + ToHexString(val[1..])
  }

  // return bytes for this hex string
  function method FromHexString(data : LooseHexString) : (ret : seq<uint8>)
    ensures |ret| == (|data| + 1) / 2
  {
    if |data| == 0 then
      []
    else if |data| % 2 == 1 then
      [HexVal(data[0])] + FromHexString(data[1..])
    else
      [HexValue(data[..2])] + FromHexString(data[2..])
  }

  lemma ToHexStringRoundTrip(s : string)
    requires IsHexString(s)
    requires |s| % 2 == 0
    ensures ToHexString(FromHexString(s)) == s
  {
    if |s| == 0 {
    }
    else if |s| == 2 {
      HexStrRoundTrip(s);
      assert FromHexString(s) == [HexValue(s[..2])];
    } else {
      HexStrRoundTrip(s[..2]);
      assert FromHexString(s[..2]) == [HexValue(s[..2])];
    }
  }

  lemma FromHexStringRoundTrip(x : seq<uint8>)
    ensures FromHexString(ToHexString(x)) == x
  {}

  lemma EmptyHexStrings()
    ensures ToHexString([]) == ""
    ensures FromHexString("") == []
  {}

}
