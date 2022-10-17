// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesHKDF {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import Digest

  method {:test} TestCase1() {
    // https://tools.ietf.org/html/rfc5869#appendix-A
    // A.1.  Test Case 1 Basic test case with SHA-256

    var hash := Primitives.Types.SHA_256;
    var IKM := [
      11, 11, 11, 11, 11, 11, 11,
      11, 11, 11, 11, 11, 11, 11,
      11, 11, 11, 11, 11, 11, 11,
      11
    ];
    var salt := [
      0, 1, 2, 3,  4,  5,
      6, 7, 8, 9, 10, 11,
      12
    ];
    var info := [
      240, 241, 242, 243,
      244, 245, 246, 247,
      248, 249
    ];
    var L := 42;

    var PRK := [
        7, 119,   9, 54,  44,  46,  50, 223,
      13, 220,  63, 13, 196, 123, 186,  99,
      144, 182, 199, 59, 181,  15, 156,  49,
      34, 236, 132, 74, 215, 194, 179, 229
    ];
    var OKM := [
      60, 178,  95,  37, 250, 172, 213, 122, 144,
      67,  79, 100, 208,  54,  47,  42,  45,  45,
      10, 144, 207,  26,  90,  76,  93, 176,  45,
      86, 236, 196, 197, 191,  52,   0, 114,   8,
      213, 184, 135,  24,  88, 101
    ];

    BasicExtractTest(
      Primitives.Types.HkdfExtractInput(
        digestAlgorithm := hash,
        salt := Some(salt),
        ikm := IKM
      ),
      PRK
    );

    BasicExpandTest(
      Primitives.Types.HkdfExpandInput(
        digestAlgorithm := hash,
        prk := PRK,
        info := info,
        expectedLength := L
      ),
      OKM
    );

    BasicHkdfTest(
      Primitives.Types.HkdfInput(
        digestAlgorithm := hash,
        salt := Some(salt),
        ikm := IKM,
        info := info,
        expectedLength := L
      ),
      OKM
    );
  }

  method BasicExtractTest(
    input: Primitives.Types.HkdfExtractInput,
    expectedPRK: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var output :- expect client.HkdfExtract(input);
    expect |output| == Digest.Length(input.digestAlgorithm);
    expect output == expectedPRK;
  }

  method BasicExpandTest(
    input: Primitives.Types.HkdfExpandInput,
    expectedOKM: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var output :- expect client.HkdfExpand(input);
    expect |output| == input.expectedLength as nat;
    expect output == expectedOKM;
  }

  method BasicHkdfTest(
    input: Primitives.Types.HkdfInput,
    expectedOKM: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var output :- expect client.Hkdf(input);
    expect |output| == input.expectedLength as nat;
    expect output == expectedOKM;
  }

}
