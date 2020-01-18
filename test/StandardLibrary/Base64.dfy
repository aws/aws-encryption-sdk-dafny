include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/Base64.dfy"

module TestBse64 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Base64 = Base64

  method {:test} TestIsBase64CharSuccess() returns (r: Result<()>) {
    var allBase64Chars := "+/0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    r := Require(forall c :: c in allBase64Chars ==> IsBase64Char(c));
  }

  method {:test} TestIsBase64CharFailure() returns (r: Result<()>) {
    var allBase64Chars := "+/0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    r := Require(forall c :: c !in allBase64Chars ==> !IsBase64Char(c));
  }

  method {:test} TestIsUnpaddedBase64StringSuccess() returns (r: Result<()>) {
    r := Require(IsUnpaddedBase64String("+0aA"));
  }

  method {:test} TestIsUnpaddedBase64StringTooShort() returns (r: Result<()>) {
    r := Require(!IsUnpaddedBase64String("+0a"));
  }

  method {:test} TestIsUnpaddedBase64StringNotBase64() returns (r: Result<()>) {
    r := Require(!IsUnpaddedBase64String("+0a$"));
  }

  method {:test} TestIndexToChar63() returns (r: Result<()>) {
    r := RequireEqual(IndexToChar(63), '/');
  }

  method {:test} TestIndexToChar62() returns (r: Result<()>) {
    r := RequireEqual(IndexToChar(62), '+');
  }

  method {:test} TestIndexToCharDigits() returns (r: Result<()>) {
    var digits := "0123456789";
    r := Require(forall i :: 52 <= i <= 61 ==> IndexToChar(i) in digits);
  }

  method {:test} TestIndexToCharLowercase() returns (r: Result<()>) {
    var lowercase := "abcdefghijklmnopqrstuvwxyz";
    r := Require(forall i :: 26 <= i <= 51 ==> IndexToChar(i) in lowercase);
  }

  method {:test} TestIndexToCharUppercase() returns (r: Result<()>) {
    var uppercase := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    r := Require(forall i :: 0 <= i <= 25 ==> IndexToChar(i) in uppercase);
  }

  method {:test} TestCharToIndex63() returns (r: Result<()>) {
    r := RequireEqual(CharToIndex('/'), 63);
  }

  method {:test} TestCharToIndex62() returns (r: Result<()>) {
    r := RequireEqual(CharToIndex('+'), 62);
  }

  method {:test} TestCharToIndexDigits() returns (r: Result<()>) {
    var digits := "0123456789";
    r := Require(forall i :: 0 <= i < |digits| ==> CharToIndex(digits[i]) == ((i + 52) as index));
  }

  method {:test} TestCharToIndexLowercase() returns (r: Result<()>) {
    var lowercase := "abcdefghijklmnopqrstuvwxyz";
    r := Require(forall i :: 0 <= i < |lowercase| ==> CharToIndex(lowercase[i]) == ((i + 26) as index));
  }

  method {:test} TestCharToIndexUppercase() returns (r: Result<()>) {
    var uppercase := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    r := Require(forall i :: 0 <= i < |uppercase| ==> CharToIndex(uppercase[i]) == (i as index));
  }

  method {:test} TestUInt24ToSeq() returns (r: Result<()>) {
    var input: uint24 := 0x100101;
    var output := [0x10, 0x1, 0x1];
    r := RequireEqual(output, UInt24ToSeq(input));
  }

  method {:test} TestSeqToUInt24() returns (r: Result<()>) {
    var input := [0x10, 0x1, 0x1];
    var output: uint24 := 0x100101;
    r := RequireEqual(output, SeqToUInt24(input));
  }

  method {:test} TestUInt24ToIndexSeq() returns (r: Result<()>) {
    var input: uint24 := 0x100101;
    var output := [0x4, 0x0, 0x4, 0x1];
    r := RequireEqual(output, UInt24ToIndexSeq(input));
  }

  method {:test} TestIndexSeqToUInt24() returns (r: Result<()>) {
    var input := [0x4, 0x0, 0x4, 0x1];
    var output: uint24 := 0x100101;
    r := RequireEqual(output, IndexSeqToUInt24(input));
  }

  method {:test} TestDecodeBlock() returns (r: Result<()>) {
    var input := [0x4, 0x0, 0x4, 0x1];
    var output := [0x10, 0x1, 0x1];
    r := RequireEqual(output, DecodeBlock(input));
  }

  method {:test} TestEncodeBlock() returns (r: Result<()>) {
    var input := [0x10, 0x1, 0x1];
    var output := [0x4, 0x0, 0x4, 0x1];
    r := RequireEqual(output, EncodeBlock(input));
  }

  method {:test} TestDecodeRecursively() returns (r: Result<()>) {
    var input := [0x4, 0x0, 0x4, 0x1, 0x4, 0x0, 0x4, 0x1];
    var output := [0x10, 0x1, 0x1, 0x10, 0x1, 0x1];
    r := RequireEqual(output, DecodeRecursively(input));
  }

  method {:test} TestEncodeRecursively() returns (r: Result<()>) {
    var input := [0x10, 0x1, 0x1, 0x10, 0x1, 0x1];
    var output := [0x4, 0x0, 0x4, 0x1, 0x4, 0x0, 0x4, 0x1];
    r := RequireEqual(output, EncodeRecursively(input));
  }

  method {:test} TestFromCharsToIndices() returns (r: Result<()>) {
    var input := "aA1+/";
    var output := [0x1A, 0x0, 0x35, 0x3E, 0x3F];
    r := RequireEqual(output, FromCharsToIndices(input));
  }

  method {:test} TestFromIndicesToChars() returns (r: Result<()>) {
    var input := [0x1A, 0x0, 0x35, 0x3E, 0x3F];
    var output := "aA1+/";
    r := RequireEqual(output, FromIndicesToChars(input));
  }

  method {:test} TestDecodeUnpadded() returns (r: Result<()>) {
    var input := "Zm9vYmFy";
    var output := [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72];
    r := RequireEqual(output, DecodeUnpadded(input));
  }

  method {:test} TestEncodeUnpadded() returns (r: Result<()>) {
    var input := [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72];
    var output := "Zm9vYmFy";
    r := RequireEqual(output, EncodeUnpadded(input));
  }

  method {:test} TestDecodeUnpaddedEmpty() returns (r: Result<()>) {
    r := RequireEqual([], DecodeUnpadded([]));
  }

  method {:test} TestEncodeUnpaddedEmpty() returns (r: Result<()>) {
    r := RequireEqual([], EncodeUnpadded([]));
  }

  method {:test} TestIs1PaddingSuccess() returns (r: Result<()>) {
    r := Require(Is1Padding("Zm8="));
  }

  method {:test} TestIs1PaddingTooShort() returns (r: Result<()>) {
    r := Require(!Is1Padding("Zm="));
  }

  method {:test} TestIs1PaddingTooLong() returns (r: Result<()>) {
    r := Require(!Is1Padding("Zm88="));
  }

  method {:test} TestIs1PaddingInvalidChar0() returns (r: Result<()>) {
    r := Require(!Is1Padding("$m8="));
  }

  method {:test} TestIs1PaddingInvalidChar1() returns (r: Result<()>) {
    r := Require(!Is1Padding("Z$8="));
  }

  method {:test} TestIs1PaddingInvalidChar2() returns (r: Result<()>) {
    r := Require(!Is1Padding("Zm$="));
  }

  method {:test} TestIs1PaddingInvalidChar3() returns (r: Result<()>) {
    r := Require(!Is1Padding("Zm8Z"));
  }

  method {:test} TestIs1PaddingInvalidChar2Modulus() returns (r: Result<()>) {
    r := Require(!Is1Padding("Zm9="));
  }

  method {:test} TestDecode1Padding() returns (r: Result<()>) {
    var input := "Zm8=";
    var output := [0x66, 0x6F];
    r := RequireEqual(output, Decode1Padding(input));
  }

  method {:test} TestEncode1Padding() returns (r: Result<()>) {
    var input := [0x66, 0x6F];
    var output := "Zm8=";
    r := RequireEqual(output, Encode1Padding(input));
  }

  method {:test} TestIs2PaddingSuccess() returns (r: Result<()>) {
    r := Require(Is2Padding("Zg=="));
  }

  method {:test} TestIs2PaddingTooShort() returns (r: Result<()>) {
    r := Require(!Is2Padding("Zg="));
  }

  method {:test} TestIs2PaddingTooLong() returns (r: Result<()>) {
    r := Require(!Is2Padding("Zgg=="));
  }

  method {:test} TestIs2PaddingInvalidChar0() returns (r: Result<()>) {
    r := Require(!Is2Padding("$g=="));
  }

  method {:test} TestIs2PaddingInvalidChar1() returns (r: Result<()>) {
    r := Require(!Is2Padding("Z$=="));
  }

  method {:test} TestIs2PaddingInvalidChar2() returns (r: Result<()>) {
    r := Require(!Is2Padding("Zgg="));
  }

  method {:test} TestIs2PaddingInvalidChar3() returns (r: Result<()>) {
    r := Require(!Is2Padding("Zg=g"));
  }

  method {:test} TestIs2PaddingInvalidChar1Modulus() returns (r: Result<()>) {
    r := Require(!Is2Padding("ZR=="));
  }

  method {:test} TestDecode2Padding() returns (r: Result<()>) {
    var input := "Zg==";
    var output := [0x66];
    r := RequireEqual(output, Decode2Padding(input));
  }

  method {:test} TestEncode2Padding() returns (r: Result<()>) {
    var input := [0x66];
    var output := "Zg==";
    r := RequireEqual(output, Encode2Padding(input));
  }
}
