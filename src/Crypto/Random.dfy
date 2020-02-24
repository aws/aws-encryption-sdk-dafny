include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module {:extern "Random"} Random {
  export
    provides GenerateBytes, StandardLibrary, UInt

  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
  {
    var randBytes := ExternGenerateBytes(i);
    if |randBytes| == i as int {
      return Success(randBytes);
    } else {
      return Failure("Incorrect length sequence from ExternGenerateBytes.");
    }
  }

  method {:extern} ExternGenerateBytes(i: int32) returns (o: seq<uint8>)
    requires 0 <= i
}
