// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module Random {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import ExternRandom
  import Types = AwsCryptographyPrimitivesTypes

  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.Error>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
  {
    var value :- ExternRandom.GenerateBytes(i);

    :- Need(
      |value| == i as int,
      Types.AwsCryptographicPrimitivesError(message := "Incorrect length from ExternRandom.")
    );

    return Success(value);
  }
}

module {:extern "ExternRandom"} ExternRandom {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.OpaqueError>)
}
