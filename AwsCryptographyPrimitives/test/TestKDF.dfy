// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"
include "../src/KDF/KdfCtr.dfy"

module TestKDF {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import Digest
  import KdfCtr

  method KdfRawDeriveTest( 
    ikm: seq<uint8>,
    info: seq<uint8>,
    L: Primitives.Types.PositiveInteger,
    expectedOKM: seq<uint8>
  )
    requires 
      && |ikm| == 32
      && L == 32
      && 4 + |info| < INT32_MAX_LIMIT
  {

    var output := KdfCtr.RawDerive(ikm, info, L, 0);

    if output.Success? {
      expect |output.value| == L as nat;
      expect output.value == expectedOKM;
    }
  }

  method KdfTest(
    input: Primitives.Types.KdfCtrInput,
    expectedOKM: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var output :- expect client.KdfCounterMode(input);
    expect |output| == input.expectedLength as nat;
    expect output == expectedOKM;
  }
}