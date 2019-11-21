include "../StandardLibrary/UInt.dfy"

module {:extern "Random"} Random {
  export
    provides GenerateBytes, UInt

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method {:extern} GenerateBytes(i: int32) returns (o: seq<uint8>)
    requires 0 <= i
    ensures |o| == i as nat
}
