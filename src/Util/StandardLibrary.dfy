module {:extern "STL"} StandardLibrary {
  datatype {:extern} Option<T> = None | Some(get: T)

  newtype byte = x | 0 <= x < 256
  type uint8 = byte

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  newtype uint32 = x | 0 <= x < 0x1_0000_0000

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
  {
    if n > 0 then [value] + Fill(value, n-1) else []
  }

}
