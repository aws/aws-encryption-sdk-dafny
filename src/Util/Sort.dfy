// adapted from dafny test Test/dafny3/GenericSort.dfy
include "../StandardLibrary/StandardLibrary.dfy"
abstract module TotalOrder {
  type T // the type to be compared
  predicate compat_mset(s : multiset<T>)
  predicate method Leq(a: T, b: T) // Leq(a,b) iff a <= b
  // Three properties of total orders.  Here, they are given as unproved
  // lemmas, that is, as axioms.
  lemma Antisymmetry(s : multiset<T>, a: T, b: T)
    requires compat_mset(s)
    requires a in s
    requires b in s
    requires Leq(a, b) && Leq(b, a)
    ensures a == b

  lemma Transitivity(s : multiset<T>, a: T, b: T, c: T)
    requires compat_mset(s)
    requires (a in s) && (b in s) && (c in s)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)
  lemma Totality(s : multiset<T>, a: T, b: T)
    requires compat_mset(s)
    requires (a in s) && (b in s)
    ensures Leq(a, b) || Leq(b, a)
}

abstract module Sort {
  import O : TotalOrder  // let O denote some module that has the members of TotalOrder

  predicate compat_arr (a : array<O.T>) reads a { O.compat_mset(multiset(a[..])) }
 
  predicate SeqSorted(s : seq<O.T>)
    {
      forall i, j :: 0 <= i < j < |s| ==> O.Leq(s[i], s[j])
    }

  predicate Sorted(a: array<O.T>, low: int, high: int)
    requires compat_arr(a)
    requires 0 <= low <= high <= a.Length
    reads a
    // The body of the predicate is hidden outside the module, but the postcondition is
    // "exported" (that is, visible, known) outside the module.  Here, we choose the
    // export the following property:
    ensures Sorted(a, low, high) ==> forall i, j :: low <= i < j < high ==> O.Leq(a[i], a[j])
    ensures Sorted(a, low, high) ==> SeqSorted(a[low..high])
  {
    forall i, j :: low <= i < j < high ==> O.Leq(a[i], a[j])
  }


  // In the insertion sort routine below, it's more convenient to keep track of only that
  // neighboring elements of the array are sorted...
  predicate NeighborSorted(a: array<O.T>, low: int, high: int)
    requires compat_arr(a)
    requires 0 <= low <= high <= a.Length
    reads a
  {
    forall i :: low < i < high ==> O.Leq(a[i-1], a[i])
  }
  // ...but we show that property to imply all pairs to be sorted.  The proof of this
  // lemma uses the transitivity property.
  lemma NeighborSorted_implies_Sorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    requires compat_arr(a)
    requires NeighborSorted(a, low, high)
    ensures Sorted(a, low, high)
    decreases high - low
  {
    if low != high {
      NeighborSorted_implies_Sorted(a, low+1, high);
      forall j | low+1 < j < high
      {
        O.Transitivity(multiset(a[..]), a[low], a[low+1], a[j]);
      }
    }
  }

  // Standard insertion sort method
  method InsertionSort(a: array<O.T>)
    modifies a
    requires compat_arr(a)
    ensures compat_arr(a)
    ensures Sorted(a, 0, a.Length)
    ensures multiset(a[..]) == old(multiset(a[..]))
  {
    if a.Length == 0 { return; }
    var i := 1;
    while i < a.Length
      invariant 0 < i <= a.Length
      invariant compat_arr(a)
      invariant NeighborSorted(a, 0, i)
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var j := i;
      while 0 < j && !O.Leq(a[j-1], a[j])
        invariant 0 <= j <= i
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant compat_arr(a)
        invariant NeighborSorted(a, 0, j)
        invariant NeighborSorted(a, j, i+1)
        invariant 0 < j < i ==> O.Leq(a[j-1], a[j+1])
      {
        // The proof of correctness uses the totality property here.
        // It implies that if two elements are not previously in
        // sorted order, they will be after swapping them.
        O.Totality(multiset(a[..]), a[j-1], a[j]);
        a[j], a[j-1] := a[j-1], a[j];
        j := j - 1;
      }
      i := i + 1;
    }
    NeighborSorted_implies_Sorted(a, 0, a.Length);
  }
}

module SeqByteOrder refines TotalOrder {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  type T = seq<uint8>
  predicate compat_mset ... { true }

  function method min (x : int, y : int) : (r : int)
    ensures x >= r
    ensures y >= r
    ensures (x == r) || (y == r) {
      if x < y then x else y
    }


  function method memcmp_le (a : seq<uint8>, b : seq<uint8>, len : nat) : (res : Option<bool>)
    requires |a| >= len
    requires |b| >= len {
    if len == 0 then None else if a[0] != b[0] then Some(a[0] < b[0]) else memcmp_le (a[1..], b[1..], len - 1)
  }

  lemma memcmp_le_none (a : seq<uint8>, b : seq<uint8>, len : nat)  
    requires |a| >= len
    requires |b| >= len
    ensures memcmp_le(a, b, len).None? <==> a[0..len] == b[0..len] {
      if len == 0 {

      }
      else {
        if (a[0] == b[0]) {
          assert (a == [a[0]] + a[1..]);
          assert (b == [b[0]] + b[1..]);
          memcmp_le_none(a[1..], b[1..], len-1);

        }
        else {

        }
      }

    }

  lemma memcmp_le_some_flip (a : seq<uint8>, b : seq<uint8>, len : nat)
    requires |a| >= len
    requires |b| >= len
    requires memcmp_le(a,b,len).Some?
    ensures memcmp_le(b,a,len).Some? && memcmp_le(a,b,len).get == !memcmp_le(b,a,len).get {

    }

  predicate method leq (a : seq<uint8>, b : seq<uint8>) {
    match memcmp_le(a,b, if |a| < |b| then |a| else |b|) {
      case Some(b) => b
      case None => |a| <= |b|
    }
  }

  predicate method Leq ... {
    leq(a,b)
  }

  lemma anti_seq (a : seq<uint8>, b : seq<uint8>)
    requires leq(a,b) && leq(b,a)
    ensures a == b { 
      memcmp_le_none(a, b, if |a| < |b| then |a| else |b|);
      memcmp_le_none(b, a, if |a| < |b| then |a| else |b|);
      if |a| == |b| {
        if (memcmp_le(a,b, |a|) == None) { }
        else {
          memcmp_le_some_flip(a, b, |a|);
        }
      }
      else {
        if (memcmp_le(a, b, if |a| < |b| then |a| else |b|) == None) {

        }
        else {
          memcmp_le_some_flip(a, b, if |a| < |b| then |a| else |b|);
        }
      }
    }

  lemma Antisymmetry ... { anti_seq(a,b); }

  // TODO
  lemma {:axiom} trans(a : seq<uint8>, b : seq<uint8>, c : seq<uint8>)
    requires leq(a,b)
    requires leq(b,c)
    ensures leq(a, c) 
      
    

  lemma Transitivity ... { trans(a,b,c); }

  lemma tot (a : seq<uint8>, b : seq<uint8>)
    ensures leq(a,b) || leq(b,a) {
      if a == [] {
        if b == [] {

        }
        else {

        }

      }
      else {
        if b == [] {

        }
        else {

          tot(a[1..], b[1..]);

        }
      }

    }

  lemma Totality ... { tot(a,b); }

}

module SeqByteKeysOrder refines TotalOrder {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import O = SeqByteOrder

  type T = (seq<uint8>, seq<uint8>)
  predicate compat_mset ... { 
    (forall i, j :: i in s ==> j in s ==> i != j ==> i.0 != j.0) && // uniq keys
    (forall i :: i in s ==> s[i] == 1) // no duplicates
     }

  predicate method Leq ... {
    O.Leq(a.0, b.0)
  }

  function keys_of_mset (s : multiset<(seq<uint8>, seq<uint8>)>) : multiset<seq<uint8>> {
    if s == multiset{} then multiset{} else (var x :| x in s; multiset{x.0} + keys_of_mset(s - multiset{x}))
  }

  lemma in_keys_of_mset (s : multiset<(seq<uint8>, seq<uint8>)>, x : (seq<uint8>, seq<uint8>))
    requires x in s
    ensures x.0 in keys_of_mset(s) {

    }

  lemma Antisymmetry ... { 
    var keys := keys_of_mset(s);
    in_keys_of_mset(s, a);
    in_keys_of_mset(s, b);
    O.Antisymmetry(keys, a.0, b.0);
  }

  lemma Transitivity ... {
    var keys := keys_of_mset(s);
    in_keys_of_mset(s, a);
    in_keys_of_mset(s, b);
    in_keys_of_mset(s, c);
    O.Transitivity(keys, a.0, b.0, c.0);
  }

  lemma Totality ... {
    var keys := keys_of_mset(s);
    in_keys_of_mset(s, a);
    in_keys_of_mset(s, b);
    O.Totality(keys, a.0, b.0);
  }
}
