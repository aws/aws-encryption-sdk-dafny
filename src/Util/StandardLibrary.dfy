module {:extern "STL"} StandardLibrary {
  datatype {:extern} Option<T> = None | Some(get: T)

  newtype byte = x | 0 <= x < 256
  type uint8 = byte

  newtype uint16 = x | 0 <= x < 0x1_0000
  const UINT16_MAX := 0x1_0000 - 1

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  newtype uint32 = x | 0 <= x < 0x1_0000_0000
  const UINT32_MAX := 0x1_0000_0000 - 1

  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }

  function method deser_uint16_from_array (p : array<byte>) : uint16
    reads p
    requires p.Length == 2
  {
    var x1 := p[0] as int * 256;
    assert x1 <= 256 * 256;
    var x := x1 + p[1] as int;
    assert x <= UINT16_MAX;
    x as uint16
  }

  function method deser_uint32_from_array (p : array<byte>) : uint32
    reads p
    requires p.Length == 4
  {
    // 2^24 = 0x100_0000
    var x3 :=      p[0] as int * 0x100_0000;
    // 2^16 = 0x1_0000
    var x2 := x3 + p[1] as int * 0x1_0000;
    // 2^8 = 0x100
    var x1 := x2 + p[2] as int * 0x100;
    // 2^0 = 0x1
    var  x := x1 + p[3] as int;
    assert x <= UINT32_MAX;
    x as uint32
  }

  datatype Either<S,T> = Left(left: S) | Right(right: T)

  datatype Error = IOError(m: string) | DeserializationError(m: string)

  type Result<T> = Either<T, Error>

  method values<A,B>(m: map<A,B>) returns (vals: seq<B>)
    ensures |vals| == |m|
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

  predicate method ltByte(a: byte, b: byte) { a < b }
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

}
