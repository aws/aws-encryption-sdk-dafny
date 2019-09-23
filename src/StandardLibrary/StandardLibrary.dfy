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
    forall i :: i in s ==> i < 256 as char
  }

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }

  method array_of_seq<T> (s : seq<T>)  returns (a : array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }

  function method {:opaque} StringToByteSeq(s: string): (s': seq<uint8>)
    requires forall i :: i in s ==> i < 256 as char
    ensures |s| == |s'| 
  {
      if s == [] then [] else  (
        assert (forall i :: i in s[1..] ==> i in s);
        [(s[0] as int % 256) as uint8] + StringToByteSeq(s[1..]))
  }

  function method {:opaque} byteseq_of_string_lossy (s : string) : (s' : seq<uint8>)
    ensures |s| == |s'|
  {
      if s == [] then [] else  (
        assert (forall i :: i in s[1..] ==> i in s);
        [(s[0] as int % 256) as uint8] + byteseq_of_string_lossy(s[1..]))
  }

  function method {:opaque} ByteSeqToString(s: seq<uint8>): (s': string)
    ensures |s| == |s'|
    ensures forall i :: i in s' ==> i < 256 as char
  {
      if s == [] then [] else [(s[0] as char)] + ByteSeqToString(s[1..])
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

  datatype gtag<A, B> = tagged(val : A, ghost tagged :  B)
    function method val<A, B>(p : gtag<A,B>) : A {
        match p
            case tagged(x,y) => x
    }

    function tag<A, B>(p: gtag<A,B>) : B {
        match p
            case tagged(x,y) => y
    }

  class mut<T> {
      var x : T
      constructor (y : T) ensures (this.x == y) {
          this.x := y;
      }
      method put(y : T) modifies this ensures (this.x == y) {
          this.x := y;
      }
      function method  get() : (y : T) reads this ensures (y == this.x) {
          this.x
      }
  }

  function method odflt<T> (o : Option<T>, x : T) : T {
    match o
      case Some(a) => a
      case None => x
  }

  function method isSome<T> (o : Option<T>) : bool {
    match o
      case Some(_) => true
      case None => false
  }

  function method isNone<T> (o : Option<T>) : bool {
    match o
      case Some(_) => false
      case None => true
  }

  predicate method uniq<T(==)>(s : seq<T>) {
    if s == [] then true else if s[0] in s[1..] then false else uniq(s[1..])
  }

  lemma uniq_idxP<T>(s : seq<T>)
    ensures uniq(s) <==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]) {

  }

  // TODO
  lemma {:axiom} uniq_multisetP<T> (s : seq<T>)
    ensures uniq(s) <==> (forall x :: x in s ==> multiset(s)[x] == 1)

  function method sum<T>(s : seq<T>, f : T -> int) : int {
      if s == [] then 0 else f(s[0]) + sum(s[1..], f)
  }

  lemma {:axiom} sum_perm<T> (s : seq <T>, s' : seq<T>, f : T -> int)
      requires multiset(s) == multiset(s')
      ensures sum(s, f) == sum(s', f)


  function count<T> (s : seq<T>, x : T) : int {
    if s == [] then 0 else (if s[0] == x then 1 else 0) + count(s[1..], x)
  }

  lemma count_ge0<T> (s : seq<T>, x : T)
    ensures 0 <= count(s, x) {
      if s == [] { }
      else {
        assert count(s, x) == (if x == s[0] then 1 else 0) + count(s[1..], x);
        count_ge0(s[1..], x);
      }
    }

  lemma count_nil<T> (x : T)
    ensures count([], x) == 0 { }

  lemma in_count_gt0P<T> (s : seq<T>, x : T)
    ensures (x in s) <==> (count(s, x) > 0) {
      if s == [] { }
      else {
        if s[0] == x {
          count_ge0(s[1..], x);
        }
        else { }
      }
    }

  lemma count_idx_gt0P<T> (s : seq<T>, i : int)
    requires (0 <= i < |s|)
    ensures count(s, s[i]) > 0 {
      assert s[i] in s;
      in_count_gt0P(s, s[i]);
    }

  lemma count_eq0P<T> (s : seq<T>, x : T)
    ensures (x !in s) <==> (count(s, x) == 0) {
      if s == [] { }
      else {
        if s[0] == x {
          assert s[0] in s;
          assert x in s;
          count_ge0(s[1..], x);
        }
        else { }
      }
    }

  lemma uniq_count_le1<T> (s : seq<T>, x : T)
    requires uniq(s)
    ensures count(s, x) <= 1 {
      if s == [] { }
      else {
        if s[0] == x {
          assert (s[0] !in s[1..]);
          count_eq0P(s[1..], x);
        }
        else { }
      }
    }

  lemma multiset_seq_count<T> (s : seq<T>, x : T)
  ensures multiset(s)[x] == count(s, x) {
    if s == [] { }
    else {
      assert s == [s[0]] + s[1..];
      assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
      assert multiset(s)[x] == multiset{s[0]}[x] + multiset(s[1..])[x];
      multiset_seq_count(s[1..], x);
    }
  }

  // TODO
  lemma {:axiom} multiset_seq_eq1<T> (s : seq<T>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures forall x :: x in multiset(s) ==> multiset(s)[x] == 1

  // TODO
  lemma {:axiom} multiset_of_seq_dup<T> (s : seq<T>, i : int, j : int)
      requires 0 <= i < j < |s|
      requires s[i] == s[j]
      ensures multiset(s)[s[i]] > 1

  lemma multiset_of_seq_gt0P<T> (s : seq<T>, x : T)
    requires multiset(s)[x] > 0
    ensures exists i :: 0 <= i < |s| && s[i] == x { }

  // TODO
  lemma {:axiom} seq_dup_multset<T> (s : seq<T>, x : T)
    requires multiset(s)[x] > 1
    ensures exists i, j :: 0 <= i < j < |s| && s[i] == s[j]


  lemma eq_multiset_seq_memP<T> (s : seq<T>, s' : seq<T>, x : T)
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
    decreases s
  {
      if s == []
      then []
      else [f(s[0])] + MapSeq(s[1..], f)
  }

  function method FlattenSeq<T>(s: seq<seq<T>>): seq<T> {
      if s == []
      then []
      else s[0] + FlattenSeq(s[1..])
  }

  predicate method uniq_fst<S(==), T(==)> (s : seq<(S, T)>) {
    uniq(MapSeq(s, (x : (S, T)) => x.0))
  }


  // TODO
  lemma {:axiom} uniq_fst_uniq<S, T> (s : seq<(S,T)>)
    requires uniq_fst(s)
    ensures uniq(s)

  // TODO
  lemma {:axiom} uniq_fst_idxP<S, T> (s : seq<(S, T)>)
    requires uniq_fst(s)
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i].0 != s[j].0

  function method min(a: int, b: int): int {
    if a < b then a else b }

  method values<A,B>(m: map<A,B>) returns (vals: seq<B>)
  {
    var keys := m.Keys;
    vals := [];
    while keys != {}
      decreases keys
      invariant |keys| + |vals| == |m.Keys|
    {
      var a :| a in keys;
      keys := keys - {a};
      vals := vals + [m[a]];
    }
  }

  predicate method ltByte(a: uint8, b: uint8) { a < b }
  predicate method ltNat (a: nat,  b: nat)  { a < b }
  predicate method ltInt (a: int,  b: int)  { a < b }

  predicate method lexCmpArrays<T(==)>(a : array<T>, b : array<T>, lt: (T, T) -> bool)
      reads a, b
  {
      a.Length == 0 || (b.Length != 0 && lexCmpArraysNonEmpty(a, b, 0, lt))
  }

  predicate method lexCmpArraysNonEmpty<T(==)>(a : array<T>, b : array<T>, i: nat, lt: (T, T) -> bool)
      requires i < a.Length
      requires i < b.Length
      requires forall j: nat :: j < i ==> a[j] == b[j]
      decreases a.Length - i
      reads a, b
  {
      if a[i] != b[i]
      then lt(a[i], b[i])
      else
          if i+1 < a.Length && i+1 < b.Length
          then lexCmpArraysNonEmpty(a, b, i+1, lt)
          else
              if i+1 == a.Length && i+1 < b.Length
              then true
              else
                  if i+1 < a.Length && i+1 == b.Length
                  then false
                  else true // i+1 == a.Length && i+1 == b.Length, i.e. a == b
  }

  lemma {:axiom} eq_multiset_eq_len<T> (s : seq<T>, s' : seq<T>)
      requires multiset(s) == multiset(s')
      ensures |s| == |s'|
}
