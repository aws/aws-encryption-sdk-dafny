// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesDigest {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt
  import Digest

  method {:test} DigestTests() {
    BasicDigestTest(
      digestAlgorithm := Primitives.Types.SHA_256,
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        240, 228, 194, 247, 108, 88, 145, 110,
        194,  88, 242,  70, 133, 27, 234,   9,
        29,  20, 212,  36, 122, 47, 195, 225,
        134, 148,  70,  27,  24, 22, 225,  59
      ]
    );

    BasicDigestTest(
      digestAlgorithm := Primitives.Types.SHA_384,
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        166, 158, 125, 243,  11,  36, 192,  66, 236,
        84,  12, 203, 189, 191, 177,  86,  44, 133,
        120, 112,  56, 200, 133, 116, 156,  30,  64,
        142,  45,  98, 250,  54, 100,  44, 208,   7,
        95, 163,  81, 232,  34, 226, 184, 165, 145,
        57, 205, 157
      ]
    );

    BasicDigestTest(
      digestAlgorithm := Primitives.Types.SHA_512,
      // The string "asdf" as bytes
      message := [ 97, 115, 100, 102 ],
      expectedDigest := [
        64,  27,   9, 234, 179, 192,  19, 212, 202, 84, 146,
        43, 184,   2, 190, 200, 253,  83,  24,  25, 43,  10,
        117, 242,   1, 216, 179, 114, 116,  41,   8, 15, 179,
        55,  89,  26, 189,  62,  68,  69,  59, 149, 69,  85,
        183, 160, 129,  46,  16, 129, 195, 155, 116,  2, 147,
        247, 101, 234, 231,  49, 245, 166,  94, 209
      ]
    );

  }

  method BasicDigestTest(
    nameonly digestAlgorithm: Primitives.Types.DigestAlgorithm,
    nameonly message: seq<uint8>,
    nameonly expectedDigest: seq<uint8>
  )
  {
    var client :- expect Primitives.AtomicPrimitives();

    var input := Primitives.Types.DigestInput(
      digestAlgorithm := digestAlgorithm,
      message := message
    );

    var output :- expect client.Digest(input);
    expect |output| == Digest.Length(digestAlgorithm);
    expect output == expectedDigest;
  }
}
