include "UInt.dfy"

module {:extern "STL"} StandardLibrary {
  import opened U = UInt

  // TODO: Depend on types defined in dafny-lang/libraries instead
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

  function method RequireEqual<T(==)>(expected: T, actual: T): (r: Result<()>) 
      ensures r.Success? ==> expected == actual
  {
    // TODO: Report message similar to "Expected ___ but got ___"
    // Blocked on https://github.com/dafny-lang/dafny/issues/450
    RequireWithMessage(expected == actual, "Failed equality")
  }
  
  function method Require(b: bool): (r: Result<()>) 
      ensures r.Success? ==> b 
  {
    RequireWithMessage(b, "Failed requirement")
  }

  function method RequireWithMessage(b: bool, message: string): (r: Result<()>) 
      ensures r.Success? ==> b 
  {
    if b then Success(()) else Failure(message)
  }
  
  function method Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
  {
    if |ss| == 1 then ss[0] else ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i := Find(s, delim, 0);
    if i.Some? then [s[..i.get]] + Split(s[(i.get + 1)..], delim) else [s]
  }

  lemma WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
  {
    calc {
      Split(s, delim);
    ==
      var i := Find(s, delim, 0);
      if i.Some? then [s[..i.get]] + Split(s[i.get + 1..], delim) else [s];
    ==  { FindLocatesElem(s, delim, 0, |prefix|); }
      [s[..|prefix|]] + Split(s[|prefix| + 1..], delim);
    ==  { assert s[..|prefix|] == prefix; }
      [prefix] + Split(s[|prefix| + 1..], delim);
    }
  }

  lemma WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
  {
    calc {
      Split(s, delim);
    ==
      var i := Find(s, delim, 0);
      if i.Some? then [s[..i.get]] + Split(s[i.get+1..], delim) else [s];
    ==  { FindLocatesElem(s, delim, 0, |s|); }
      [s];
    }
  }

  lemma FindLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures Find(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
    {}

  function method Find<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==>  i <= index.get < |s| && s[index.get] == c && c !in s[i..index.get]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    if i == |s| then None
    else if s[i] == c then Some(i)
    else Find(s, c, i + 1)
  }

  function method Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
  {
    if |s| == 0 then []
    else if f(s[0]) then ([s[0]] + Filter(s[1..], f))
    else Filter(s[1..], f)
  }

  lemma FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
  {
    if s == [] {
      assert s + s' == s';
    } else {
      FilterIsDistributive<T>(s[1..], s', f);
      assert s + s' == [s[0]] + (s[1..] + s');
      assert Filter(s + s', f) == Filter(s, f) + Filter(s', f);
    }
  }

  function method Min(a: int, b: int): int {
    if a < b then a else b
  }

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    seq(n, _ => value)
  }

  method SeqToArray<T>(s: seq) returns (a: array)
    // "Fresh" expressions require editing memory
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
  {}

  /*
   * Lexicographic comparison of sequences.
   *
   * Given two sequences `a` and `b` and a strict (that is, irreflexive)
   * ordering `less` on the elements of these sequences, determine whether or not
   * `a` is lexicographically "less than or equal to" `b`.
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
    lengthOfCommonPrefix <= |b|
    && (forall i :: 0 <= i < lengthOfCommonPrefix ==> a[i] == b[i])
    && (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
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
}
