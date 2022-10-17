// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestAwsCryptographyPrimitivesGenerateRandomBytes {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt

  method {:test} BasicGenerateRandomBytes() {
    var client :- expect Primitives.AtomicPrimitives();
    var length := 5 as int32;

    var input := Primitives.Types.GenerateRandomBytesInput(
      length := length
    );

    var output := client.GenerateRandomBytes(input);

    var value :- expect output;
    expect |value| == length as int;
  }
}
