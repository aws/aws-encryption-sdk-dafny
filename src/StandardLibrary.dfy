// =============== Basic library stuff ===============

module StandardLibrary {
  export
    reveals byte, Option, ArrayMaxLength
    provides Fill
 
  datatype Option<T> = None | Some(get: T)

  newtype byte = x | 0 <= x < 256
 
  // Array max length in C# (but not in Go or JavaScript)
  const ArrayMaxLength := 0x7FFF_FFFF

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }
 
}