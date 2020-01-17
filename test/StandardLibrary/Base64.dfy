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

  method {:test} TestIsUnpaddedStringSuccess() returns (r: Result<()>) {
    r := Require(IsUnpaddedString("+0aA"));
  }

  method {:test} TestIsUnpaddedStringTooShort() returns (r: Result<()>) {
    r := Require(!IsUnpaddedString("+0a"));
  }

  method {:test} TestIsUnpaddedStringNotBase64() returns (r: Result<()>) {
    r := Require(!IsUnpaddedString("+0a$"));
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

  method {:test} TestBase64ToSeq() returns (r: Result<()>) {
    var input: base64 := 0x100101;
    var output := [0x10, 0x1, 0x1];
    r := RequireEqual(output, Base64ToSeq(input));
  }

  method {:test} TestSeqToBase64() returns (r: Result<()>) {
    var input := [0x10, 0x1, 0x1];
    var output: base64 := 0x100101;
    r := RequireEqual(output, SeqToBase64(input));
  }

  method {:test} TestBase64ToIndexSeq() returns (r: Result<()>) {
    var input: base64 := 0x100101;
    var output := [0x4, 0x0, 0x4, 0x1];
    r := RequireEqual(output, Base64ToIndexSeq(input));
  }

  method {:test} TestIndexSeqToBase64() returns (r: Result<()>) {
    var input := [0x4, 0x0, 0x4, 0x1];
    var output: base64 := 0x100101;
    r := RequireEqual(output, IndexSeqToBase64(input));
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
    var output := [26, 0, 53, 62, 63];
    r := RequireEqual(output, FromCharsToIndices(input));
  }

  method {:test} TestFromIndicesToChars() returns (r: Result<()>) {
    var input := [26, 0, 53, 62, 63];
    var output := "aA1+/";
    r := RequireEqual(output, FromIndicesToChars(input));
  }
}
