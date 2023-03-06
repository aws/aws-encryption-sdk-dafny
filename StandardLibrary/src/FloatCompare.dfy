// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"
include "StandardLibrary.dfy" 

/*
  Compare two strings as floating point numbers.

  The only method you should be concerned about is

  function method CompareFloat(x : string, y : string) : (ret : int) 

    returns -1 if x < y    // a.k.a. FloatCompare.Less
    returns  1 if x > y    // a.k.a. FloatCompare.Equal
    returns  0 if x == y   // a.k.a. FloatCompare.Greater
  
  Note that CompareFloat never fails. For any two strings, it will come up with an answer.
*/

module FloatCompare {
  import opened Wrappers
  import opened StandardLibrary

  newtype CompareType = x : int | -1 <= x <= 1
  const Less : CompareType := -1
  const Equal : CompareType := 0
  const Greater : CompareType := 1

  // base 10 string to integer
  // unspecified results of any characters are not decimal digits
  function method {:tailrecursion} StrToIntInner(s : string, acc : int := 0) : int
  {
    if |s| == 0 then
      acc
    else if '0' <= s[0] <= '9' then
      StrToIntInner(s[1..], acc * 10 + s[0] as int - '0' as int)
    else
      StrToIntInner(s[1..], acc)
  }

  // return the input string with leading space removed
  // space is defined as numeric values 0..32
  function method {:tailrecursion} SkipLeadingSpace(val : string) : (ret : string)
    ensures |ret| == 0 || ret[0] > ' '
  {
    if |val| > 0 && val[0] <= ' ' then
      SkipLeadingSpace(val[1..])
    else
      val
  }

  // remove leading space, then convert to integer
  function method {:tailrecursion} StrToInt(s : string, acc : int := 0) : int
  {
    var tmp := SkipLeadingSpace(s);
    if |tmp| == 0 then
      0
    else if tmp[0] == '-' then
      -StrToIntInner(s)
    else
      StrToIntInner(s)
  }

  // split on 'e' or 'E'
  function method SplitE(x : string) :  Option<(string, string)>
  {
    var parts := SplitOnce?(x, 'e');
    if parts.Some? then
      parts
    else
      SplitOnce?(x, 'E')
  }

  // split the exponent from the number
  function method SplitExp(x : string) :  (string, int)
  {
    var parts := SplitE(x);
    if parts.Some? then
      (parts.value.0, StrToInt(parts.value.1))
    else
      (x, 0)
  }

  // return the input string with leading zeros removed
  function method {:tailrecursion} SkipLeadingZeros(val : string) : (ret : string)
    ensures |ret| == 0 || ret[0] != '0'
  {
    if |val| > 0 && val[0] == '0' then
      SkipLeadingZeros(val[1..])
    else
      val
  }

  // return the input string with trailing zeros removed
  function method {:tailrecursion} SkipTrailingZeros(val : string) : (ret : string)
    ensures |ret| == 0 || ret[|ret|-1] != '0'
  {
    if |val| > 0 && val[|val|-1] == '0' then
      SkipTrailingZeros(val[..|val|-1])
    else
      val
  }

  // split on decimal point, remove unneeded zeros
  function method SplitDot(x : string) :  (string, string)
  {
    var parts := SplitOnce?(x, '.');
    if parts.Some? then
      (SkipLeadingZeros(parts.value.0), SkipTrailingZeros(parts.value.1))
    else
      (SkipLeadingZeros(x), "")
  }

  // compare two strings
  function method StrCmp(x : string, y : string) : (ret : CompareType)
  {
    if |x| == 0 && |y| == 0 then
      0
    else if |x| == 0 then
      -1
    else if |y| == 0 then
      1
    else if x[0] < y[0] then
      -1
    else if x[0] > y[0] then
      1
    else
      StrCmp(x[1..], y[1..])
  }

  lemma StrCmpSymmetric(x : string, y : string)
  ensures StrCmp(x,y) == -StrCmp(y,x)
  {}

  // compare two positive floats
  function method CompareFloatInner(x : string, y : string) : (ret : CompareType) 
  {
    var xParts := SplitExp(x);
    var yParts := SplitExp(y);
    
    var xNum := SplitDot(xParts.0);
    var yNum := SplitDot(yParts.0);

    var logX := xParts.1 + |xNum.0|;
    var logY := yParts.1 + |yNum.0|;

    if logX > logY then
      1
    else if logY > logX then
      -1
    else
      var nX := xNum.0 + xNum.1;
      var nY := yNum.0 + yNum.1;
      StrCmp(nX, nY)
  }

  predicate method IsNegative(x: string)
  {
    |x| > 0 && x[0] == '-'
  }

  function method CompareFloat(x : string, y : string) : (ret : CompareType) 
  {
    var x := SkipLeadingSpace(x);
    var y := SkipLeadingSpace(y);

    if IsNegative(x) && IsNegative(y) then
      CompareFloatInner(y[1..], x[1..])
    else if IsNegative(x) then
      -1
    else if IsNegative(y) then
      1
    else
      CompareFloatInner(x, y)
  }
}