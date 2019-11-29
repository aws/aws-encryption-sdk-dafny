include "../../src/Util/UTF8.dfy"

module TestUTF8 {
  import opened StandardLibrary
  import UTF8

  function {:test} EncodeHappyCase(): Result<()> {
    var unicodeString := "abc\u0306\u01FD\u03B2";
    var expectedBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];

    var result :- UTF8.Encode(unicodeString);
    RequireEqual(expectedBytes, result)
  }

  function {:test} EncodeInvalidUnicode(): Result<UTF8.ValidUTF8Bytes> {
    // Create string with UTF-16 surrogate (\uD800)
    var invalidUnicode := "abc\uD800";

    UTF8.Encode(invalidUnicode)
  }

  function {:test} DecodeHappyCase(): Result<()> {
    var unicodeBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var expectedString := "abc\u0306\u01FD\u03B2";

    var result :- UTF8.Decode(unicodeBytes);
    RequireEqual(expectedString, result)
  }

  function {:test} DecodeInvalidUnicode(): Result<string> {
    // Create byte sequence with UTF-16 surrogate (0xEDA080)
    var invalidUnicode := [0x61, 0x62, 0x63, 0xED, 0xA0, 0x80];
    UTF8.Decode(invalidUnicode)
  }
}
