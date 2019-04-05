module StandardLibrary {
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
}
