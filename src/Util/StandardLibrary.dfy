module {:extern "STL"} StandardLibrary {
  datatype {:extern} Option<T> = None | Some(get: T)

  newtype byte = x | 0 <= x < 256
  type uint8 = byte

  newtype uint16 = x | 0 <= x < 0x10000
  const UINT16_MAX := 0x10000 - 1

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  newtype uint32 = x | 0 <= x < 0x1_0000_0000

  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  // Array max length in C# (but not in Go or JavaScript)
  const ArrayMaxLength := 0x7FFF_FFFF

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }


  function method ser_uint16 (x : uint16) : (byte, byte) {
    var b1 : byte := (x / 256) as byte;
    var b2 : byte := (x % 256) as byte;
    (b1, b2)
  }

  function method deser_uint16 (p : (byte, byte)) : uint16 {
    var x1 := (p.0 as int) * 256;
    assert (x1 <= (256 * 256));
    var x := x1 + (p.1 as int);
    assert (x <= UINT16_MAX);
    (x as uint16)
  }

  lemma ser_uint16K (x : uint16)
  ensures deser_uint16(ser_uint16(x)) == x { }

  lemma deser_uint16K (p : (byte, byte)) 
  ensures ser_uint16(deser_uint16(p)) == p { }

  function method nseq<A> (x : A, n : nat) : (xs : seq<A>)
    ensures (|xs| == n) 
  {
      if n == 0 then []
      else [x] + (nseq(x, n-1))
  }

  method array_of_seq<T> (s : seq<T>)  returns (a : array<T>)
    ensures fresh(a) 
    ensures a.Length == |s| 
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }

  function method byteseq_of_string (s : string) : (s' : seq<byte>)
    requires forall i :: i in s ==> i < 256 as char
    ensures |s| == |s'| 
  {
      if s == [] then [] else  (
        assert (forall i :: i in s[1..] ==> i in s);
        [(s[0] as int % 256) as byte] + byteseq_of_string(s[1..]))
  }

  function method byteseq_of_string_unsafe (s : string) : (s' : seq<byte>)
    ensures |s| == |s'|
  {
      if s == [] then [] else  (
        assert (forall i :: i in s[1..] ==> i in s);
        [(s[0] as int % 256) as byte] + byteseq_of_string_unsafe(s[1..]))
  }

  function method string_of_byteseq (s : seq<byte>) : (s' : string)
    ensures |s| == |s'| 
    ensures forall i :: i in s' ==> i < 256 as char
  {
      if s == [] then [] else [(s[0] as char)] + string_of_byteseq(s[1..])
  }

  lemma string_byteseqK (s : string)
    requires forall i :: i in s ==> i < 256 as char
    ensures string_of_byteseq(byteseq_of_string(s)) == s {
      if s == [] {

      }
      else {
        assert (s[0] in s);
        assert (((s[0] as int % 256) as char) == s[0]);
        assert (forall i :: i in s[1..] ==> i in s);
      }
    }

  lemma byteseq_stringK (s : seq<byte>)
    ensures byteseq_of_string(string_of_byteseq(s)) == s {

    }

  method StringToByteArray(s: string) returns (a: array<byte>)
    ensures fresh(a) && a.Length <= 2 * |s|
  {
    // Assume all 8-bit characters for now
    a := new byte[|s|];
    forall i | 0 <= i < |s| {
      a[i] := (s[i] as int % 256) as byte;
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
      function method  get() : (x : T) reads this ensures (x == this.x) {
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

  function method seq_map<S, T>(s : seq<S>, f : S -> T) : seq<T> {
    if s == [] then [] else
    [f(s[0])] + seq_map(s[1..], f)
  }

  predicate method uniq_fst<S(==), T(==)> (s : seq<(S, T)>) {
    uniq(seq_map(s, (x : (S, T)) => x.0))
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

  datatype Either<S,T> = Left(left: S) | Right(right: T)

  datatype Error = IOError(m: string)

  method values<A,B>(m: map<A,B>) returns (vals: seq<B>)
  {
    var keys := m.Keys;
    vals := [];
    while keys != {}
      decreases keys
    {
      var a :| a in keys;
      keys := keys - {a};
      vals := vals + [m[a]];
    }
  }
  

  lemma {:axiom} eq_multiset_eq_len<T> (s : seq<T>, s' : seq<T>)
      requires multiset(s) == multiset(s')
      ensures |s| == |s'| 

}
