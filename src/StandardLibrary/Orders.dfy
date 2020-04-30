include "UInt.dfy"
  
module {:extern "STLOrders"} StandardLibrary.Orders {
  export
    reveals Reflexive, AntiSymmetric, Transitive, Connected, TotalOrdering, Trichotomous
    reveals LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow
    provides UInt
    
  import opened UInt

  /*
   * Properties of relations
   *
   */
  
  predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }
  
  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool) {
    forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z)
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && AntiSymmetric(R)
    && Transitive(R)
    && Connected(R)
  }

  /*
   * For an ordering "R" to be _trichotomous_ means that for any two "x" and "y",
   * EXACTLY one of the following three conditions holds:
   *   - R(x, y)
   *   - x == y
   *   - R(y, x)
   * Note that being trichotomous implies being irreflexive.
   */
  predicate Trichotomous<T(!new)>(R: (T, T) -> bool) {
    (forall x, y :: R(x, y) || x == y || R(y, x)) &&  // at least one of the three
    (forall x, y :: R(x, y) && R(y, x) ==> false) &&  // not both of the R's
    (forall x, y :: R(x, y) ==> x != y)  // not an R and the equality
  }

  /*
   * Useful orderings
   *
   * In what follows, the identifier "less" is used to denote a relation
   * that is irreflexive, like "<" on numbers. The identifier "below" is used
   * to denote a relation that is reflexive, like "<=" on numbers.
   */

  /*
   * Here is an example relation and a lemma that says the relation is appropriate for use in
   * lexicographic orderings.
   */

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  /*
   * Reflexive lexicographical comparison of byte sequences
   */
  
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
    assert Transitive(LexicographicByteSeqBelow) by {
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
}
