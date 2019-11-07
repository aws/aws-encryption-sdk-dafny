// RUN: %dafny "./UTF8.dfy" "../../src/extern/dotnet/UTF8.cs" /compile:3 > "%t" && rm "./UTF8.cs"
// RUN: %diff "%s.expect" "%t"

include "../../src/Util/UTF8.dfy"

module TestUTF8 {
  import UTF8

  method TestEncodeHappyCase() {
    var unicodeString := "abc\u0306\u01FD\u03B2";
    var expectedBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];

    var result := UTF8.Encode(unicodeString);
    if result.Success? && result.value == expectedBytes {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestEncodeInvalidUnicode() {
    // Create string with UTF-16 surrogate (\uD800)
    var invalidUnicode := "abc\uD800";

    var result := UTF8.Encode(invalidUnicode);
    if result.Failure? {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

    method TestDecodeHappyCase() {
    var unicodeBytes := [0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
    var expectedString := "abc\u0306\u01FD\u03B2";

    var result := UTF8.Decode(unicodeBytes);
    if result.Success? && result.value == expectedString {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestDecodeInvalidUnicode() {
    // Create byte sequence with UTF-16 surrogate (0xEDA080)
    var invalidUnicode := [0x61, 0x62, 0x63, 0xED, 0xA0, 0x80];

    var result := UTF8.Decode(invalidUnicode);
    if result.Failure? {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    TestEncodeHappyCase();
    TestEncodeInvalidUnicode();
    TestDecodeHappyCase();
    TestDecodeInvalidUnicode();
  }
}
