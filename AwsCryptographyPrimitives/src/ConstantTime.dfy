// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
  Constant Time Comparison of byte sequences.

  USAGE : ConstantTime.Equals(a,b)
  Does the same as "a == b" but slower, and in constant time.
*/

include "../../StandardLibrary/src/UInt.dfy"

module ConstantTime {
  import opened StandardLibrary.UInt

  // sequences are equal if zero is returned
  // Some care should be taken to ensure that target languages don't over optimize this.
  function method {:tailrecursion} Compare(a : seq<uint8>, b : seq<uint8>, acc : bv8 := 0) : bv8
    requires |a| == |b|
  {
    if |a| == 0 then
      acc
    else
      var x := ((a[0] as bv8) ^ (b[0] as bv8));
      Compare(a[1..], b[1..], x | acc)
  }

  predicate method Equals(a : seq<uint8>, b : seq<uint8>)
    requires |a| == |b|
  {
    Compare(a, b) == 0
  }
}
