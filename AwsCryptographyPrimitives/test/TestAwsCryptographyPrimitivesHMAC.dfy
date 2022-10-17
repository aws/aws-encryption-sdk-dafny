// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesHMAC {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt
  import Digest

  method {:test} HMACTests() {

    BasicHMACTest(
      digestAlgorithm := Primitives.Types.SHA_256,
      key := [1,2,3,4],
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        55, 107, 186, 241,  51, 255, 154,
        169, 106, 133,   2, 248,  54, 230,
        193, 147, 212, 179, 154,  66,  43,
        52, 108, 181, 144, 152,  19, 101,
        117,  99, 204, 134
      ]
    );

    BasicHMACTest(
      digestAlgorithm := Primitives.Types.SHA_384,
      key := [1,2,3,4],
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        90, 206, 234,  81, 173,  76, 235, 148, 203, 139,
        195,  46, 251,  14,  97, 110, 146,  49, 147,  24,
        240,   1,  17, 231,  58, 104, 146,  53, 144, 167,
        11, 112,   7,  39, 122,  15,  58,  53, 144,  91,
        16, 223,  51,  98,  30,  88,  23, 166
      ]
    );

    BasicHMACTest(
      digestAlgorithm := Primitives.Types.SHA_512,
      key := [1,2,3,4],
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        100,  23, 173, 215,  39,  67,  51, 165, 149,  53,  87,
        84, 145,  58, 221, 155, 239, 182, 249, 134, 147, 191,
        143, 224, 140, 165, 190, 221, 183,  15,   6, 102, 203,
        77, 238,  64,  10, 138,  61,  64, 219,  79, 248, 249,
        90, 102, 217, 188,  13,   2, 101,  96, 217, 242,  73,
        254, 190, 217, 134,  33, 163, 137, 151, 183
      ]
    );

  }

  method BasicHMACTest(
    nameonly digestAlgorithm: Primitives.Types.DigestAlgorithm,
    nameonly key: seq<uint8>,
    nameonly message: seq<uint8>,
    nameonly expectedDigest: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var input := Primitives.Types.HMacInput(
      digestAlgorithm := digestAlgorithm,
      key := key,
      message := message
    );

    var output :- expect client.HMac(input);
    expect |output| == Digest.Length(digestAlgorithm);
    expect output == expectedDigest;
  }
}
