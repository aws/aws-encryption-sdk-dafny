include "UInt.dfy"

module {:extern "STL"} StandardLibrary {
  import opened U = UInt

  datatype Option<T> = None | Some(get: T)
  {
    function method ToResult(): Result<T> {
      match this
      case Some(v) => Success(v)
      case None() => Failure("Option is None")
    }
    function method GetOrElse(default: T): T {
      match this
      case Some(v) => v
      case None => default
    }
  }

  datatype Either<S,T> = Left(left: S) | Right(right: T)

  datatype Error = IOError(msg: string) | DeserializationError(msg: string) | SerializationError(msg: string) | Error(msg : string)

  datatype Result<T> = Success(value: T) | Failure(error: string)
  {
    predicate method IsFailure() {
      Failure?
    }
    function method PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure(this.error)
    }
    function method Extract(): T
      requires Success?
    {
      value
    }
    function method ToOption(): Option<T> {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }
    function method GetOrElse(default: T): T {
      match this
      case Success(s) => s
      case Failure(e) => default
    }
  }

  predicate StringIs8Bit(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] < 256 as char
  }

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    seq(n, _ => value)
  }

  method array_of_seq<T> (s : seq<T>)  returns (a : array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }

  function method {:opaque} StringToByteSeq(s: string): (s': seq<uint8>)
    requires StringIs8Bit(s)
    ensures |s| == |s'| 
  {
    seq(|s|, i requires 0 <= i < |s| => s[i] as uint8)
  }

  function method {:opaque} StringToByteSeqLossy(s: string): (s': seq<uint8>)
    ensures |s| == |s'|
  {
    seq(|s|, i requires 0 <= i < |s| => (s[i] as uint16 % 256) as uint8)
  }

  function method {:opaque} ByteSeqToString(s: seq<uint8>): (s': string)
    ensures |s| == |s'|
    ensures StringIs8Bit(s')
  {
    seq(|s|, i requires 0 <= i < |s| => s[i] as char)
  }

  lemma StringByteSeqCorrect(s: string)
    requires StringIs8Bit(s)
    ensures ByteSeqToString(StringToByteSeq(s)) == s
  {
    reveal ByteSeqToString(), StringToByteSeq();
    if s == [] {
    } else {
      assert s[0] in s;
      assert (s[0] as int % 256) as char == s[0];
      assert forall i :: i in s[1..] ==> i in s;
    }
  }

  lemma ByteSeqStringCorrect(s: seq<uint8>)
    ensures StringToByteSeq(ByteSeqToString(s)) == s
  {
    reveal ByteSeqToString(), StringToByteSeq();
  }

  method StringToByteArray(s: string) returns (a: array<uint8>)
    ensures fresh(a) && a.Length <= 2 * |s|
  {
    // Assume all 8-bit characters for now
    a := new uint8[|s|];
    forall i | 0 <= i < |s| {
      a[i] := (s[i] as int % 256) as uint8;
    }
  }

  class mut<T> {
    var x: T
    constructor (y: T)
      ensures x == y
    {
      x := y;
    }
    method put(y: T)
      modifies this
      ensures x == y
    {
      x := y;
    }
    function method get(): (y: T)
      reads this
      ensures y == x
    {
      x
    }
  }

  predicate method uniq<T(==)>(s: seq<T>) {
    if s == [] then true else if s[0] in s[1..] then false else uniq(s[1..])
  }

  lemma uniq_idxP<T>(s: seq<T>)
    ensures uniq(s) <==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
  {
  }

  // TODO
  lemma {:axiom} uniq_multisetP<T>(s: seq<T>)
    ensures uniq(s) <==> (forall x :: x in s ==> multiset(s)[x] == 1)

  function method sum<T>(s: seq<T>, f: T -> int): int {
    if s == [] then 0 else f(s[0]) + sum(s[1..], f)
  }

  lemma {:axiom} sum_perm<T>(s: seq <T>, s': seq<T>, f: T -> int)
    requires multiset(s) == multiset(s')
    ensures sum(s, f) == sum(s', f)


  function count<T>(s: seq<T>, x: T): int {
    if s == [] then 0 else (if s[0] == x then 1 else 0) + count(s[1..], x)
  }

  lemma count_ge0<T>(s: seq<T>, x: T)
    ensures 0 <= count(s, x)
  {
    if s == [] {
    } else {
      assert count(s, x) == (if x == s[0] then 1 else 0) + count(s[1..], x);
      count_ge0(s[1..], x);
    }
  }

  lemma count_nil<T>(x: T)
    ensures count([], x) == 0
  { }

  lemma in_count_gt0P<T>(s: seq<T>, x: T)
    ensures (x in s) <==> (count(s, x) > 0)
  {
    if s != [] && s[0] == x {
      count_ge0(s[1..], x);
    }
  }

  lemma count_idx_gt0P<T>(s: seq<T>, i: int)
    requires 0 <= i < |s|
    ensures count(s, s[i]) > 0
  {
    assert s[i] in s;
    in_count_gt0P(s, s[i]);
  }

  lemma count_eq0P<T>(s: seq<T>, x: T)
    ensures (x !in s) <==> (count(s, x) == 0)
  {
    if s != [] && s[0] == x {
      assert s[0] in s;
      assert x in s;
      count_ge0(s[1..], x);
    }
  }

  lemma uniq_count_le1<T>(s: seq<T>, x: T)
    requires uniq(s)
    ensures count(s, x) <= 1
  {
    if s != [] && s[0] == x {
      assert (s[0] !in s[1..]);
      count_eq0P(s[1..], x);
    }
  }

  lemma multiset_seq_count<T>(s: seq<T>, x: T)
    ensures multiset(s)[x] == count(s, x)
  {
    if s == [] {
    } else {
      assert s == [s[0]] + s[1..];
      assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
      assert multiset(s)[x] == multiset{s[0]}[x] + multiset(s[1..])[x];
      multiset_seq_count(s[1..], x);
    }
  }

  // TODO
  lemma {:axiom} multiset_seq_eq1<T>(s: seq<T>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures forall x :: x in multiset(s) ==> multiset(s)[x] == 1

  // TODO
  lemma {:axiom} multiset_of_seq_dup<T>(s: seq<T>, i: int, j: int)
    requires 0 <= i < j < |s|
    requires s[i] == s[j]
    ensures multiset(s)[s[i]] > 1

  lemma multiset_of_seq_gt0P<T>(s: seq<T>, x: T)
    requires multiset(s)[x] > 0
    ensures exists i :: 0 <= i < |s| && s[i] == x
  { }

  // TODO
  lemma {:axiom} seq_dup_multset<T>(s: seq<T>, x: T)
    requires multiset(s)[x] > 1
    ensures exists i, j :: 0 <= i < j < |s| && s[i] == s[j]


  lemma eq_multiset_seq_memP<T>(s: seq<T>, s': seq<T>, x: T)
    requires multiset(s) == multiset(s')
    ensures (x in s) == (x in s')
  {
    if x in s {
      assert x in multiset(s);
      assert x in multiset(s');
      assert x in s';
    }
    else {
      assert x !in multiset(s);
      assert x !in multiset(s');
      assert x !in s';
    }
  }

  function method MapSeq<S, T>(s: seq<S>, f: S ~> T): seq<T>
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i,o | 0 <= i < |s| && o in f.reads(s[i]) :: o
    decreases |s|
  {
    if s == [] then [] else [f(s[0])] + MapSeq(s[1..], f)
  }

  function method FlattenSeq<T>(s: seq<seq<T>>): seq<T> {
    if s == [] then [] else s[0] + FlattenSeq(s[1..])
  }

  predicate method uniq_fst<S(==), T(==)>(s: seq<(S, T)>) {
    uniq(MapSeq(s, (x: (S, T)) => x.0))
  }


  // TODO
  lemma {:axiom} uniq_fst_uniq<S, T>(s: seq<(S,T)>)
    requires uniq_fst(s)
    ensures uniq(s)

  // TODO
  lemma {:axiom} uniq_fst_idxP<S, T>(s: seq<(S, T)>)
    requires uniq_fst(s)
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i].0 != s[j].0

  function method min(a: int, b: int): int {
    if a < b then a else b
  }

  // TODO
  method values<A,B>(m: map<A,B>) returns (vals: seq<B>) {
    var keys := m.Keys;
    vals := [];
    while keys != {}
      invariant |keys| + |vals| == |m.Keys|
      decreases keys
    {
      var a :| a in keys;
      keys := keys - {a};
      vals := vals + [m[a]];
    }
  }

  lemma {:axiom} eq_multiset_eq_len<T>(s: seq<T>, s': seq<T>)
    requires multiset(s) == multiset(s')
    ensures |s| == |s'|

  predicate method UInt8Less(a: uint8, b: uint8) { a < b }
  predicate method NatLess(a: nat, b: nat)  { a < b }
  predicate method IntLess(a: int, b: int)  { a < b }

  /*
   * Lexicographic comparison of sequences.
   *
   * Given two sequences `a` and `b` and a strict (that is, irreflexive)
   * ordering `less` on the elements of these sequences, `LexCmpSeqs(a, b, less)`
   * says whether or not `a` is lexicographically "less than or equal to" `b`.
   *
   * `a` is lexicographically "less than or equal to" `b` holds iff
   *   there exists a `k` such that
   *   - the first `k` elements of `a` and `b` are the same
   *   - either:
   *      -- `a` has length `k` (that is, `a` is a prefix of `b`)
   *      -- `a[k]` is strictly less (using `less`) than `b[k]`
   */

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool) {
    exists k :: 0 <= k <= |a| && LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i :: 0 <= i < lengthOfCommonPrefix ==> a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| ||
     (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  /*
   * For an ordering `less` to be _trichotomous_ means that for any two `x` and `y`,
   * exactly one of the following three conditions holds:
   *   - less(x, y)
   *   - x == y
   *   - less(y, x)
   * Note that being trichotomous implies being irreflexive. The definition of
   * `Trichotomous` here allows overlap between the three conditions, which lets us
   * think of non-strict orderings (like "less than or equal" as opposed to just
   * "less than") as being trichotomous.
   */

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool) {
    forall t, t' :: less(t, t') || t == t' || less(t', t)
  }

  /*
   * If an ordering `less` is trichotomous, then so is the irreflexive lexicographic
   * order built around `less`.
   */

  lemma LexPreservesTrichotomy<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || a == b || LexicographicLessOrEqual(b, a, less)
  {
    var m := 0;
    while m < |a| && m < |b| && a[m] == b[m]
      invariant m <= |a| && m <= |b|
      invariant forall i :: 0 <= i < m ==> a[i] == b[i]
    {
      m := m + 1;
    }
    // m is the length of the common prefix of a and b
    if m == |a| == |b| {
      assert a == b;
    } else if m == |a| < |b| {
      assert LexicographicLessOrEqualAux(a, b, less, m);
    } else if m == |b| < |a| {
      assert LexicographicLessOrEqualAux(b, a, less, m);
    } else {
      assert m < |a| && m < |b|;
      if
      case less(a[m], b[m]) =>
        assert LexicographicLessOrEqualAux(a, b, less, m);
      case less(b[m], a[m]) =>
        assert LexicographicLessOrEqualAux(b, a, less, m);
    }
  }

  function method Filter<T>(s: seq<T>, f: T -> bool): seq<T>
    ensures forall i :: 0 <= i < |s| && f(s[i]) ==> s[i] in Filter(s, f)
    ensures forall i :: 0 <= i < |Filter(s,f)| ==> Filter(s,f)[i] in s
  {
    if |s| == 0 then []
    else if f(s[0]) then ([s[0]] + Filter(s[1..], f))
    else Filter(s[1..], f)
  }

  lemma FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s+s', f) == Filter(s,f) + Filter(s',f)
  {
    if s == [] {
      assert s + s' == s';
    } else {
      FilterIsDistributive<T>(s[1..], s', f);
      assert s + s' == [s[0]] + (s[1..] + s');
      assert Filter(s+s', f) == Filter(s,f) + Filter(s',f);
    }
  }
}
