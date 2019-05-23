// =============== Basic library stuff ===============

module StandardLibrary {
  export
    reveals byte, WrapIntoByte, Option, Integer_Upper_Bound
    provides MulLemma, Fill, SeqPrefixLemma, SplitArray
 
  datatype Option<T> = None | Some(get: T)

  newtype byte = x | 0 <= x < 256

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000


  method StringToByteArray(s: string) returns (a: array<byte>)
    ensures fresh(a) && a.Length <= 2 * |s|
  {
    // Assume all 8-bit characters for now
    a := new byte[|s|];
    forall i | 0 <= i < |s| {
      a[i] := (s[i] as int % 256) as byte;
    }
  }

  function method WrapIntoByte(y: int): byte
    requires 0 <= y < 256
  {
    y as byte
  }
 
  // The Java library defines Integer.MAX_VALUE as 0x7fff_ffff.
  const Integer_Upper_Bound := 0x8000_0000

  // multiplication with a non-negative number is monotonic
  lemma MulLemma(a: int, b: int, n: nat)
    requires a <= b
    ensures a*n <= b*n
  {
  }
 
  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }
 
  lemma SeqPrefixLemma<T>(a: seq<T>, b: seq<T>, n: nat)
    requires n <= |a| && a <= b
    ensures a[..n] == b[..n]
  {
  }
 
  lemma SplitArray<T>(a: array<T>, m: nat, n: nat)
    requires m + n <= a.Length
    ensures a[..m+n] == a[..m] + a[m..m+n]
  {
  }
}