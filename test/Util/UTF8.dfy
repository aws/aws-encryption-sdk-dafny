include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/UTF8.dfy"

module TestUTF8 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened UTF8

  method {:test} TestEncodeHappyCase() returns (r: TestResult) {
    var unicodeString := "abc\u0306\u01FD\u03B2";
    var expectedBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var encoded :- UTF8.Encode(unicodeString);
    r := RequireEqual(expectedBytes, encoded);
  }

  method {:test} TestEncodeInvalidUnicode() returns (r: TestResult) {
    // Create string with UTF-16 surrogate (\uD800)
    var invalidUnicode := "abc\uD800";
    var encoded := UTF8.Encode(invalidUnicode);
    r := RequireFailure(encoded);
  }

  method {:test} TestDecodeHappyCase() returns (r: TestResult) {
    var unicodeBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var expectedString := "abc\u0306\u01FD\u03B2";
    var decoded :- UTF8.Decode(unicodeBytes);
    r := RequireEqual(expectedString, decoded);
  }

  method {:test} TestDecodeInvalidUnicode() returns (r: TestResult) {
    // Create byte sequence with UTF-16 surrogate (0xEDA080)
    var invalidUnicode := [0x61, 0x62, 0x63, 0xED, 0xA0, 0x80];
    r := Require(!ValidUTF8Seq(invalidUnicode));
  }

  method {:test} Test1Byte() returns (r: TestResult) {
    // Null
    var decoded := "\u0000";
    var encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x00], encoded);
    :- Require(Uses1Byte(encoded));
    var redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Space
    decoded := "\u0020";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x20], encoded);
    :- Require(Uses1Byte(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    decoded := "$";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x24], encoded);
    :- Require(Uses1Byte(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    decoded := "0";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x30], encoded);
    :- Require(Uses1Byte(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    decoded := "A";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x41], encoded);
    :- Require(Uses1Byte(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    decoded := "a";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0x61], encoded);
    :- Require(Uses1Byte(encoded));
    redecoded :- UTF8.Decode(encoded);
    r := RequireEqual(decoded, redecoded);
  }

  method {:test} Test2Bytes() returns (r: TestResult) {
    // British pound
    var decoded := "\u00A3";
    var encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xC2, 0xA3], encoded);
    :- Require(Uses2Bytes(encoded));
    var redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Copyright
    decoded := "\u00A9";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xC2, 0xA9], encoded);
    :- Require(Uses2Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Registered
    decoded := "\u00AE";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xC2, 0xAE], encoded);
    :- Require(Uses2Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Greek Pi
    decoded := "\u03C0";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xCF, 0x80], encoded);
    :- Require(Uses2Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    r := RequireEqual(decoded, redecoded);
  }

  method {:test} Test3Bytes() returns (r: TestResult) {
    // Enter symbol
    var decoded := "\u2386";
    var encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xE2, 0x8E, 0x86], encoded);
    :- Require(Uses3Bytes(encoded));
    var redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Alternative key
    decoded := "\u2387";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xE2, 0x8E, 0x87], encoded);
    :- Require(Uses3Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Hourglass emoji
    decoded := "\u231B";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xE2, 0x8C, 0x9B], encoded);
    :- Require(Uses3Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Modifier letter cyrillic EN
    decoded := "\u1D78";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xE1, 0xB5, 0xB8], encoded);
    :- Require(Uses3Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Chinese cat (mao)
    decoded := "\u732B";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xE7, 0x8C, 0xAB], encoded);
    :- Require(Uses3Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    r := RequireEqual(decoded, redecoded);
  }

  method {:test} Test4Bytes() returns (r: TestResult) {
    // Cuneiform Sign A - represented as a surrogate of U+12000
    var decoded := "\uD808\uDC00";
    var encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xF0, 0x92, 0x80, 0x80], encoded);
    :- Require(Uses4Bytes(encoded));
    var redecoded :- UTF8.Decode(encoded);
    :- RequireEqual(decoded, redecoded);

    // Mathematical Sans-Serif Bold Italic Small Psi - represented as a surrogate of U+1D7C1
    decoded := "\uD835\uDFC1";
    encoded :- UTF8.Encode(decoded);
    :- RequireEqual([0xF0, 0x9D, 0x9F, 0x81], encoded);
    :- Require(Uses4Bytes(encoded));
    redecoded :- UTF8.Decode(encoded);
    r := RequireEqual(decoded, redecoded);
  }
}
