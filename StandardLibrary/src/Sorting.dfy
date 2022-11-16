// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"
include "./UInt.dfy"

module Sorting {
  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering
    reveals LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow
    provides SelectionSort
    provides StandardLibrary, UInt

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt

  /*
   * Properties of relations
   */

  predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && AntiSymmetric(R)
    && StandardLibrary.Transitive(R)
    && Connected(R)
  }

  /*
   * Useful orderings
   */

  // reflexivelexicographical comparison of byte sequences
  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>) {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    || n == |x|
    || (n != |y| && x[n] < y[n])
    || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
    assert Reflexive(LexicographicByteSeqBelow) by {
      forall x, n | 0 <= n <= |x| {
        AboutLexicographicByteSeqBelowAux_Reflexive(x, n);
      }
    }
    assert AntiSymmetric(LexicographicByteSeqBelow) by {
      forall x, y, n: nat |
        n <= |x| && n <= |y| && x[..n] == y[..n] &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
      {
        AboutLexicographicByteSeqBelowAux_AntiSymmetric(x, y, n);
      }
    }
    assert StandardLibrary.Transitive(LexicographicByteSeqBelow) by {
      forall x, y, z, n: nat |
        n <= |x| && n <= |y| && n <= |z| &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
      {
        AboutLexicographicByteSeqBelowAux_Transitive(x, y, z, n);
      }
    }
    assert Connected(LexicographicByteSeqBelow) by {
      forall x, y, n: nat | n <= |x| && n <= |y| {
        AboutLexicographicByteSeqBelowAux_Connected(x, y, n);
      }
    }
  }

  lemma AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  /*
   * Sorting routines
   */

  method SelectionSort<Data>(a: array<Data>, below: (Data, Data) -> bool)
    requires StandardLibrary.Transitive(below)
    requires Connected(below)
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> below(a[i], a[j])
  {
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall i, j :: 0 <= i < j < m ==> below(a[i], a[j])
      invariant forall i, j :: 0 <= i < m <= j < a.Length ==> below(a[i], a[j])
    {
      // pick mindex to be the index of the smallest element in a[m..]
      var mindex, n := m, m + 1;
      while n < a.Length
        invariant m <= mindex < n <= a.Length
        invariant forall i :: m <= i < n ==> below(a[mindex], a[i])
      {
        if !below(a[mindex], a[n]) {
          mindex := n;
        }
        n := n + 1;
      }
      a[m], a[mindex] := a[mindex], a[m];
      m := m + 1;
    }
  }
}
