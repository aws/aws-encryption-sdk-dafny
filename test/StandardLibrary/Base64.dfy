include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/Base64.dfy"

module TestBse64 {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Base64 = Base64

  // Test vector sample encode/decode strings from https://tools.ietf.org/rfc/rfc4648.txt
  const BASE64_TEST_VECTORS_ENCODED := ["", "Zg==", "Zm8=", "Zm9v", "Zm9vYg==", "Zm9vYmE=", "Zm9vYmFy"];
  const BASE64_TEST_VECTORS_DECODED := ["", "f", "fo", "foo", "foob", "fooba", "foobar"];

  const BASE64_TEST_VECTORS_DECODED_UINT8: seq<seq<uint8>> :=
    [[], [0x66], [0x66, 0x6F], [0x66, 0x6F, 0x6F], [0x66, 0x6F, 0x6F, 0x62],
    [0x66, 0x6F, 0x6F, 0x62, 0x61], [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72]];

  const BASE64_CHARS := "+/0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

  method {:test} TestIsBase64CharSuccess() returns (r: Result<()>) {
    r := Require(forall c :: c in BASE64_CHARS ==> IsBase64Char(c));
  }

  method {:test} TestIsBase64CharFailure() returns (r: Result<()>) {
    r := Require(forall c :: c !in BASE64_CHARS ==> !IsBase64Char(c));
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

  method {:test} TestIsBase64StringTestVectors() returns (r: Result<()>) {
    r := Require(forall i :: i in BASE64_TEST_VECTORS_ENCODED ==> IsBase64String(i) == true);
  }

  method {:test} TestIsBase64StringBadLength() returns (r: Result<()>) {
    r := Require(!IsBase64String("Zg="));
  }

  method {:test} TestIsBase64StringBadString() returns (r: Result<()>) {
    r := Require(!IsBase64String("Z1=="));
  }

  method {:test} TestSanityCheckDecodedTestVectors() returns (r: Result<()>) {

    var testVectorIndex := 0;
    while testVectorIndex < |BASE64_TEST_VECTORS_DECODED|
      invariant 0 <= testVectorIndex <= |BASE64_TEST_VECTORS_DECODED|
    {
      var uint8Message: seq<uint8> := [];
      var strMessage := BASE64_TEST_VECTORS_DECODED[testVectorIndex];
      var msgIndex := 0;
      while msgIndex < |strMessage|
        invariant 0 <= msgIndex <= |strMessage|
      {
        uint8Message := uint8Message + [strMessage[msgIndex] as uint8];
        msgIndex := msgIndex + 1;
      }
      var _ :- RequireEqual(BASE64_TEST_VECTORS_DECODED_UINT8[testVectorIndex], uint8Message);
      testVectorIndex := testVectorIndex + 1;
    }
    r := Require(true);
  }

  method {:test} TestDecodeValidTestVectors() returns (r: Result<()>) {
    r := Require(forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      DecodeValid(BASE64_TEST_VECTORS_ENCODED[i]) == BASE64_TEST_VECTORS_DECODED_UINT8[i]);
  }

  method {:test} TestDecodeTestVectors() returns (r: Result<()>) {
    r := Require(forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      Decode(BASE64_TEST_VECTORS_ENCODED[i]) == Success(BASE64_TEST_VECTORS_DECODED_UINT8[i]));
  }

  method {:test} TestDecodeFailure() returns (r: Result<()>) {
    r := RequireEqual(Failure("The encoding is malformed"), Decode("$"));
  }

  method {:test} TestEncode() returns (r: Result<()>) {
    r := Require(forall i :: 0 <= i < |BASE64_TEST_VECTORS_DECODED_UINT8| ==>
      Encode(BASE64_TEST_VECTORS_DECODED_UINT8[i]) == BASE64_TEST_VECTORS_ENCODED[i]);
  }

  method {:test} TestEncodeDecode() returns (r: Result<()>) {
    r := Require(forall i :: 0 <= i < |BASE64_TEST_VECTORS_DECODED_UINT8| ==>
      Decode(Encode(BASE64_TEST_VECTORS_DECODED_UINT8[i])) == Success(BASE64_TEST_VECTORS_DECODED_UINT8[i]));
  }

  method {:test} TestDecodeEncode() returns (r: Result<()>) {
    r := Require(forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      (Decode(BASE64_TEST_VECTORS_ENCODED[i]).Success?
      && Encode(Decode(BASE64_TEST_VECTORS_ENCODED[i]).value) == BASE64_TEST_VECTORS_ENCODED[i]));
  }
}
