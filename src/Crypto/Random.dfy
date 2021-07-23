// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"

module Random {
  export
    provides GenerateBytes, StandardLibrary, UInt

  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import ExternRandom

  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
  {
    var result := ExternRandom.GenerateBytes(i);
    if result.Success? && |result.value| != i as int {
        return Failure("Incorrect length from ExternRandom.");
    }
    return result;
  }
}

module {:extern "ExternRandom"} ExternRandom {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>>)
}
