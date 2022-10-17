// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"
include "TestAwsCryptographyPrimitivesHKDF.dfy"

module TestHKDF_Rfc5869TestVectors {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened TestAwsCryptographyPrimitivesHKDF

  // https://tools.ietf.org/html/rfc5869#appendix-A
  const testVectors: seq<RFCTestVector> := [a1, a2, a3, a4, a5, a6, a7];

    //   A.1.  Test Case 1

    //  Basic test case with SHA-256

    //  Hash = SHA-256
    //  IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
    //  salt = 0x000102030405060708090a0b0c (13 octets)
    //  info = 0xf0f1f2f3f4f5f6f7f8f9 (10 octets)
    //  L    = 42

    //  PRK  = 0x077709362c2e32df0ddc3f0dc47bba63
    //         90b6c73bb50f9c3122ec844ad7c2b3e5 (32 octets)
    //  OKM  = 0x3cb25f25faacd57a90434f64d0362f2a
    //         2d2d0a90cf1a5a4c5db02d56ecc4c5bf
    //         34007208d5b887185865 (42 octets)
    const a1 := RFCTestVector(
      name := "A.1.  Test Case 1",
      hash := Primitives.Types.SHA_256,
      IKM := [
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11
      ],
      salt := [
        0, 1, 2, 3,  4,  5,
        6, 7, 8, 9, 10, 11,
        12
      ],
      info := [
        240, 241, 242, 243,
        244, 245, 246, 247,
        248, 249
      ],
      L := 42 as int32,
      PRK := [
          7, 119,   9, 54,  44,  46,  50, 223,
        13, 220,  63, 13, 196, 123, 186,  99,
        144, 182, 199, 59, 181,  15, 156,  49,
        34, 236, 132, 74, 215, 194, 179, 229
      ],
      OKM := [
        60, 178,  95,  37, 250, 172, 213, 122, 144,
        67,  79, 100, 208,  54,  47,  42,  45,  45,
        10, 144, 207,  26,  90,  76,  93, 176,  45,
        86, 236, 196, 197, 191,  52,   0, 114,   8,
        213, 184, 135,  24,  88, 101
      ]
    );

    // A.2.  Test Case 2

    // Test with SHA-256 and longer inputs/outputs

    // Hash = SHA-256
    // IKM  = 0x000102030405060708090a0b0c0d0e0f
    //       101112131415161718191a1b1c1d1e1f
    //       202122232425262728292a2b2c2d2e2f
    //       303132333435363738393a3b3c3d3e3f
    //       404142434445464748494a4b4c4d4e4f (80 octets)
    // salt = 0x606162636465666768696a6b6c6d6e6f
    //       707172737475767778797a7b7c7d7e7f
    //       808182838485868788898a8b8c8d8e8f
    //       909192939495969798999a9b9c9d9e9f
    //       a0a1a2a3a4a5a6a7a8a9aaabacadaeaf (80 octets)
    // info = 0xb0b1b2b3b4b5b6b7b8b9babbbcbdbebf
    //       c0c1c2c3c4c5c6c7c8c9cacbcccdcecf
    //       d0d1d2d3d4d5d6d7d8d9dadbdcdddedf
    //       e0e1e2e3e4e5e6e7e8e9eaebecedeeef
    //       f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff (80 octets)
    // L    = 82

    // PRK  = 0x06a6b88c5853361a06104c9ceb35b45c
    //       ef760014904671014a193f40c15fc244 (32 octets)
    // OKM  = 0xb11e398dc80327a1c8e7f78c596a4934
    //       4f012eda2d4efad8a050cc4c19afa97c
    //       59045a99cac7827271cb41c65e590e09
    //       da3275600c2f09b8367793a9aca3db71
    //       cc30c58179ec3e87c14c01d5c1f3434f
    //       1d87 (82 octets)
    const {:vcs_split_on_every_assert} a2 := RFCTestVector(
      name := "A.2.  Test Case 2",
      hash := Primitives.Types.SHA_256,
      IKM := [
        0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11,
        12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
        36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
        60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
        72, 73, 74, 75, 76, 77, 78, 79
      ],
      salt := [
        96,  97,  98,  99, 100, 101, 102, 103, 104, 105, 106,
        107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
        118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
        129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
        140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
        151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161,
        162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
        173, 174, 175
      ],
      info := [
        176, 177, 178, 179, 180, 181, 182, 183, 184, 185,
        186, 187, 188, 189, 190, 191, 192, 193, 194, 195,
        196, 197, 198, 199, 200, 201, 202, 203, 204, 205,
        206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
        216, 217, 218, 219, 220, 221, 222, 223, 224, 225,
        226, 227, 228, 229, 230, 231, 232, 233, 234, 235,
        236, 237, 238, 239, 240, 241, 242, 243, 244, 245,
        246, 247, 248, 249, 250, 251, 252, 253, 254, 255
      ],
      L := 82 as int32,
      PRK := [
          6, 166, 184, 140,  88, 83,  54, 26,
          6,  16,  76, 156, 235, 53, 180, 92,
        239, 118,   0,  20, 144, 70, 113,  1,
        74,  25,  63,  64, 193, 95, 194, 68
      ],
      OKM := [
        177,  30,  57, 141, 200,   3,  39, 161, 200, 231, 247, 140,
        89, 106,  73,  52,  79,   1,  46, 218,  45,  78, 250, 216,
        160,  80, 204,  76,  25, 175, 169, 124,  89,   4,  90, 153,
        202, 199, 130, 114, 113, 203,  65, 198,  94,  89,  14,   9,
        218,  50, 117,  96,  12,  47,   9, 184,  54, 119, 147, 169,
        172, 163, 219, 113, 204,  48, 197, 129, 121, 236,  62, 135,
        193,  76,   1, 213, 193, 243,  67,  79,  29, 135
      ]
    );

    // A.3.  Test Case 3

    // Test with SHA-256 and zero-length salt/info

    // Hash = SHA-256
    // IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
    // salt = (0 octets)
    // info = (0 octets)
    // L    = 42

    // PRK  = 0x19ef24a32c717b167f33a91d6f648bdf
    //       96596776afdb6377ac434c1c293ccb04 (32 octets)
    // OKM  = 0x8da4e775a563c18f715f802a063c5a31
    //       b8a11f5c5ee1879ec3454e5f3c738d2d
    //       9d201395faa4b61a96c8 (42 octets)
    const a3 := RFCTestVector(
      name := "A.3.  Test Case 3",
      hash := Primitives.Types.SHA_256,
      IKM := [
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11
      ],
      salt := [],
      info := [],
      L := 42 as int32,
      PRK := [
        25, 239,  36, 163,  44, 113, 123,  22,
        127,  51, 169,  29, 111, 100, 139, 223,
        150,  89, 103, 118, 175, 219,  99, 119,
        172,  67,  76,  28,  41,  60, 203,   4
      ],
      OKM := [
        141, 164, 231, 117, 165,  99, 193, 143, 113,
        95, 128,  42,   6,  60,  90,  49, 184, 161,
        31,  92,  94, 225, 135, 158, 195,  69,  78,
        95,  60, 115, 141,  45, 157,  32,  19, 149,
        250, 164, 182,  26, 150, 200
      ]
    );

    // A.4.  Test Case 4

    // Basic test case with SHA-1

    // Hash = SHA-1
    // IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b (11 octets)
    // salt = 0x000102030405060708090a0b0c (13 octets)
    // info = 0xf0f1f2f3f4f5f6f7f8f9 (10 octets)
    // L    = 42

    // PRK  = 0x9b6c18c432a7bf8f0e71c8eb88f4b30baa2ba243 (20 octets)
    // OKM  = 0x085a01ea1b10f36933068b56efa5ad81
    //       a4f14b822f5b091568a9cdd4f155fda2
    //       c22e422478d305f3f896 (42 octets)
    const a4 := RFCTestVector(
      name := "A.4.  Test Case 4",
      hash := Primitives.Types.SHA_1,
      IKM := [
        11, 11, 11, 11, 11,
        11, 11, 11, 11, 11,
        11
      ],
      salt := [
        0, 1, 2, 3,  4,  5,
        6, 7, 8, 9, 10, 11,
        12
      ],
      info := [
        240, 241, 242, 243,
        244, 245, 246, 247,
        248, 249
      ],
      L := 42 as int32,
      PRK := [
        155, 108,  24, 196,  50, 167,
        191, 143,  14, 113, 200, 235,
        136, 244, 179,  11, 170,  43,
        162,  67
      ],
      OKM := [
        8,  90,  1, 234,  27,  16, 243, 105,  51,
        6, 139, 86, 239, 165, 173, 129, 164, 241,
        75, 130, 47,  91,   9,  21, 104, 169, 205,
        212, 241, 85, 253, 162, 194,  46,  66,  36,
        120, 211,  5, 243, 248, 150
      ]
    );

    // A.5.  Test Case 5

    // Test with SHA-1 and longer inputs/outputs

    // Hash = SHA-1
    // IKM  = 0x000102030405060708090a0b0c0d0e0f
    //       101112131415161718191a1b1c1d1e1f
    //       202122232425262728292a2b2c2d2e2f
    //       303132333435363738393a3b3c3d3e3f
    //       404142434445464748494a4b4c4d4e4f (80 octets)
    // salt = 0x606162636465666768696a6b6c6d6e6f
    //       707172737475767778797a7b7c7d7e7f
    //       808182838485868788898a8b8c8d8e8f
    //       909192939495969798999a9b9c9d9e9f
    //       a0a1a2a3a4a5a6a7a8a9aaabacadaeaf (80 octets)
    // info = 0xb0b1b2b3b4b5b6b7b8b9babbbcbdbebf
    //       c0c1c2c3c4c5c6c7c8c9cacbcccdcecf
    //       d0d1d2d3d4d5d6d7d8d9dadbdcdddedf
    //       e0e1e2e3e4e5e6e7e8e9eaebecedeeef
    //       f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff (80 octets)
    // L    = 82

    // PRK  = 0x8adae09a2a307059478d309b26c4115a224cfaf6 (20 octets)
    // OKM  = 0x0bd770a74d1160f7c9f12cd5912a06eb
    //       ff6adcae899d92191fe4305673ba2ffe
    //       8fa3f1a4e5ad79f3f334b3b202b2173c
    //       486ea37ce3d397ed034c7f9dfeb15c5e
    //       927336d0441f4c4300e2cff0d0900b52
    //       d3b4 (82 octets)
    const {:vcs_split_on_every_assert} a5 := RFCTestVector(
      name := "A.5.  Test Case 5",
      hash := Primitives.Types.SHA_1,
      IKM := [
        0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11,
        12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
        36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
        60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
        72, 73, 74, 75, 76, 77, 78, 79
      ],
      salt := [
        96,  97,  98,  99, 100, 101, 102, 103, 104, 105, 106,
        107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
        118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
        129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
        140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
        151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161,
        162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
        173, 174, 175
      ],
      info := [
        176, 177, 178, 179, 180, 181, 182, 183, 184, 185,
        186, 187, 188, 189, 190, 191, 192, 193, 194, 195,
        196, 197, 198, 199, 200, 201, 202, 203, 204, 205,
        206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
        216, 217, 218, 219, 220, 221, 222, 223, 224, 225,
        226, 227, 228, 229, 230, 231, 232, 233, 234, 235,
        236, 237, 238, 239, 240, 241, 242, 243, 244, 245,
        246, 247, 248, 249, 250, 251, 252, 253, 254, 255
      ],
      L := 82 as int32,
      PRK := [
        138, 218, 224, 154, 42,  48,
        112,  89,  71, 141, 48, 155,
        38, 196,  17,  90, 34,  76,
        250, 246
      ],
      OKM := [
        11, 215, 112, 167,  77,  17,  96, 247, 201, 241,  44, 213,
        145,  42,   6, 235, 255, 106, 220, 174, 137, 157, 146,  25,
        31, 228,  48,  86, 115, 186,  47, 254, 143, 163, 241, 164,
        229, 173, 121, 243, 243,  52, 179, 178,   2, 178,  23,  60,
        72, 110, 163, 124, 227, 211, 151, 237,   3,  76, 127, 157,
        254, 177,  92,  94, 146, 115,  54, 208,  68,  31,  76,  67,
          0, 226, 207, 240, 208, 144,  11,  82, 211, 180
      ]
    );

    // A.6.  Test Case 6

    // Test with SHA-1 and zero-length salt/info

    // Hash = SHA-1
    // IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
    // salt = (0 octets)
    // info = (0 octets)
    // L    = 42

    // PRK  = 0xda8c8a73c7fa77288ec6f5e7c297786aa0d32d01 (20 octets)
    // OKM  = 0x0ac1af7002b3d761d1e55298da9d0506
    //       b9ae52057220a306e07b6b87e8df21d0
    //       ea00033de03984d34918 (42 octets)
    const a6 := RFCTestVector(
      name := "A.6.  Test Case 6",
      hash := Primitives.Types.SHA_1,
      IKM := [
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11, 11, 11, 11, 11, 11, 11,
        11
      ],
      salt := [],
      info := [],
      L := 42 as int32,
      PRK := [
        218, 140, 138, 115, 199, 250,
        119,  40, 142, 198, 245, 231,
        194, 151, 120, 106, 160, 211,
        45,   1
      ],
      OKM := [
        10, 193, 175, 112,   2, 179, 215,  97, 209,
        229,  82, 152, 218, 157,   5,   6, 185, 174,
        82,   5, 114,  32, 163,   6, 224, 123, 107,
        135, 232, 223,  33, 208, 234,   0,   3,  61,
        224,  57, 132, 211,  73,  24
      ]
    );

    // A.7.  Test Case 7

    // Test with SHA-1, salt not provided (defaults to HashLen zero octets),
    // zero-length info

    // Hash = SHA-1
    // IKM  = 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c (22 octets)
    // salt = not provided (defaults to HashLen zero octets)
    // info = (0 octets)
    // L    = 42

    // PRK  = 0x2adccada18779e7c2077ad2eb19d3f3e731385dd (20 octets)
    // OKM  = 0x2c91117204d745f3500d636a62f64f0a
    //       b3bae548aa53d423b0d1f27ebba6f5e5
    //       673a081d70cce7acfc48 (42 octets)
    const a7 := RFCTestVector(
      name := "A.7.  Test Case 7",
      hash := Primitives.Types.SHA_1,
      IKM := [
        12, 12, 12, 12, 12, 12, 12,
        12, 12, 12, 12, 12, 12, 12,
        12, 12, 12, 12, 12, 12, 12,
        12
      ],
      salt := [],
      info := [],
      L := 42 as int32,
      PRK := [
        42, 220, 202, 218,  24, 119,
        158, 124,  32, 119, 173,  46,
        177, 157,  63,  62, 115,  19,
        133, 221
      ],
      OKM := [
        44, 145,  17, 114,   4, 215,  69, 243,  80,
        13,  99, 106,  98, 246,  79,  10, 179, 186,
        229,  72, 170,  83, 212,  35, 176, 209, 242,
        126, 187, 166, 245, 229, 103,  58,   8,  29,
        112, 204, 231, 172, 252,  72
      ]
    );

  method {:test} ExpectRFCTestVectors() {
    for i := 0 to |testVectors| {
      ExpectTestVector(testVectors[i]);
    }
  }

  method ExpectTestVector(vector: RFCTestVector) {
    var RFCTestVector(name, hash, IKM, salt, info, L, PRK, OKM) := vector;
    print name + "\n";

    BasicExtractTest(
      Primitives.Types.HkdfExtractInput(
        digestAlgorithm := hash,
        salt := if |salt| > 0 then Some(salt) else None,
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
        salt := if |salt| > 0 then Some(salt) else None,
        ikm := IKM,
        info := info,
        expectedLength := L
      ),
      OKM
    );
  }

  datatype RFCTestVector = RFCTestVector(
    nameonly name: string,
    nameonly hash: Primitives.Types.DigestAlgorithm,
    nameonly IKM: seq<uint8>,
    nameonly salt: seq<uint8>,
    nameonly info: seq<uint8>,
    nameonly L: Primitives.Types.PositiveInteger,
    nameonly PRK: seq<uint8>,
    nameonly OKM: seq<uint8>
  )

}
