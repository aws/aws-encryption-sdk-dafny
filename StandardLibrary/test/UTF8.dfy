// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/UTF8.dfy"

module TestUTF8 {
  import opened UInt = StandardLibrary.UInt
  import opened UTF8

  method {:test} TestEncodeHappyCase() {
    var unicodeString := "abc\u0306\u01FD\u03B2";
    var expectedBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var encoded :- expect UTF8.Encode(unicodeString);
    expect expectedBytes == encoded;
  }

  method {:test} TestEncodeInvalidUnicode() {
    // Create string with UTF-16 surrogate (\uD800)
    var invalidUnicode := "abc\uD800";
    var encoded := UTF8.Encode(invalidUnicode);
    expect encoded.Failure?;
  }

  method {:test} TestDecodeHappyCase() {
    var unicodeBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    assert UTF8.Uses2Bytes([0xC7, 0xBD, 0xCE, 0xB2]);
    assert [0xC7, 0xBD, 0xCE, 0xB2] == unicodeBytes[5..9];
    assert UTF8.ValidUTF8Range(unicodeBytes, 7, 9);
    assert UTF8.ValidUTF8Range(unicodeBytes, 0, 9);
    var expectedString := "abc\u0306\u01FD\u03B2";
    var decoded :- expect UTF8.Decode(unicodeBytes);
    expect expectedString == decoded;
  }

  method {:test} TestDecodeInvalidUnicode() {
    // Create byte sequence with UTF-16 surrogate (0xEDA080)
    var invalidUnicode := [0x61, 0x62, 0x63, 0xED, 0xA0, 0x80];
    expect !ValidUTF8Seq(invalidUnicode);
    expect UTF8.Decode(invalidUnicode).Failure?;
  }

  method {:test} Test1Byte() {
    // Null
    var decoded := "\u0000";
    var encoded :- expect UTF8.Encode(decoded);
    expect [0x00] == encoded;
    expect Uses1Byte(encoded);
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Space
    decoded := "\u0020";
    encoded :- expect UTF8.Encode(decoded);
    expect [0x20] == encoded;
    expect Uses1Byte(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    decoded := "$";
    encoded :- expect UTF8.Encode(decoded);
    expect [0x24] == encoded;
    expect Uses1Byte(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    decoded := "0";
    encoded :- expect UTF8.Encode(decoded);
    expect [0x30] == encoded;
    expect Uses1Byte(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    decoded := "A";
    encoded :- expect UTF8.Encode(decoded);
    expect [0x41] == encoded;
    expect Uses1Byte(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    decoded := "a";
    encoded :- expect UTF8.Encode(decoded);
    expect [0x61] == encoded;
    expect Uses1Byte(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;
  }

  method {:test} Test2Bytes() {
    // British pound
    var decoded := "\u00A3";
    var encoded :- expect UTF8.Encode(decoded);
    expect [0xC2, 0xA3] == encoded;
    expect Uses2Bytes(encoded);
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Copyright
    decoded := "\u00A9";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xC2, 0xA9] == encoded;
    expect Uses2Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Registered
    decoded := "\u00AE";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xC2, 0xAE] == encoded;
    expect Uses2Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Greek Pi
    decoded := "\u03C0";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xCF, 0x80] == encoded;
    expect Uses2Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;
  }

  method {:test} Test3Bytes() {
    // Enter symbol
    var decoded := "\u2386";
    var encoded :- expect UTF8.Encode(decoded);
    expect [0xE2, 0x8E, 0x86] == encoded;
    expect Uses3Bytes(encoded);
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Alternative key
    decoded := "\u2387";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xE2, 0x8E, 0x87] == encoded;
    expect Uses3Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Hourglass emoji
    decoded := "\u231B";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xE2, 0x8C, 0x9B] == encoded;
    expect Uses3Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Modifier letter cyrillic EN
    decoded := "\u1D78";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xE1, 0xB5, 0xB8] == encoded;
    expect Uses3Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Chinese cat (mao)
    decoded := "\u732B";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xE7, 0x8C, 0xAB] == encoded;
    expect Uses3Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;
  }

  method {:test} Test4Bytes() {
    // Cuneiform Sign A - represented as a surrogate of U+12000
    var decoded := "\uD808\uDC00";
    var encoded :- expect UTF8.Encode(decoded);
    expect [0xF0, 0x92, 0x80, 0x80] == encoded;
    expect Uses4Bytes(encoded);
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;

    // Mathematical Sans-Serif Bold Italic Small Psi - represented as a surrogate of U+1D7C1
    decoded := "\uD835\uDFC1";
    encoded :- expect UTF8.Encode(decoded);
    expect [0xF0, 0x9D, 0x9F, 0x81] == encoded;
    expect Uses4Bytes(encoded);
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded;
  }
}
