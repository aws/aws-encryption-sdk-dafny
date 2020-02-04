include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/UTF8.dfy"

module TestUTF8 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened UTF8

  method {:test} EncodeHappyCase() returns (r: Result<()>) {
    var unicodeString := "abc\u0306\u01FD\u03B2";
    var expectedBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var encoded :- UTF8.Encode(unicodeString);
    r := RequireEqual(expectedBytes, encoded);
  }

  method {:test} EncodeInvalidUnicode() returns (r: Result<()>) {
    // Create string with UTF-16 surrogate (\uD800)
    var invalidUnicode := "abc\uD800";
    var encoded := UTF8.Encode(invalidUnicode);
    r := RequireFailure(encoded);
  }

  method {:test} DecodeHappyCase() returns (r: Result<()>) {
    var unicodeBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var expectedString := "abc\u0306\u01FD\u03B2";
    var decoded :- UTF8.Decode(unicodeBytes);
    r := RequireEqual(expectedString, decoded);
  }

  method {:test} DecodeInvalidUnicode() returns (r: Result<()>) {
    // Create byte sequence with UTF-16 surrogate (0xEDA080)
    var invalidUnicode := [0x61, 0x62, 0x63, 0xED, 0xA0, 0x80];
    r := Require(!ValidUTF8Seq(invalidUnicode));
  }
}
