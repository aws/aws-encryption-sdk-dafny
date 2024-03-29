// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/Base64.dfy"

module TestBase64 {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened Base64 = Base64

  const BASE64_TEST_VECTORS_ENCODED := ["", "VA==", "VGU=", "VGVz", "VGVzdA==", "VGVzdGk=", "VGVzdGlu", "VGVzdGluZw==",
    "VGVzdGluZys=", "VGVzdGluZysx"];
  const BASE64_TEST_VECTORS_DECODED := ["", "T", "Te", "Tes", "Test", "Testi", "Testin", "Testing", "Testing+",
    "Testing+1"];

  const BASE64_TEST_VECTORS_DECODED_UINT8: seq<seq<uint8>> :=
    [[], [0x54], [0x54, 0x65], [0x54, 0x65, 0x73], [0x54, 0x65, 0x73, 0x74], [0x54, 0x65, 0x73, 0x74, 0x69],
    [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E], [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E, 0x67],
    [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E, 0x67, 0x2B], [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E, 0x67, 0x2B, 0x31]];

  const BASE64_CHARS := "+/0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

  lemma {:axiom} Base64TestVectorIsValid(i: int)
    requires 0 <= i < |BASE64_TEST_VECTORS_ENCODED|
    ensures IsBase64String(BASE64_TEST_VECTORS_ENCODED[i])

  method {:test} TestIsBase64CharSuccess() {
    expect forall c :: c in BASE64_CHARS ==> IsBase64Char(c);
  }

  method {:test} TestIsBase64CharFailure() {
    expect forall c :: c !in BASE64_CHARS ==> !IsBase64Char(c);
  }

  method {:test} TestIsUnpaddedBase64StringSuccess() {
    expect IsUnpaddedBase64String("VGVz");
  }

  method {:test} TestIsUnpaddedBase64StringTooShort() {
    expect !IsUnpaddedBase64String("VGV");
  }

  method {:test} TestIsUnpaddedBase64StringNotBase64() {
    expect !IsUnpaddedBase64String("VGV$");
  }

  method {:test} TestIndexToChar63() {
    expect IndexToChar(63) == '/';
  }

  method {:test} TestIndexToChar62() {
    expect IndexToChar(62) == '+';
  }

  method {:test} TestIndexToCharDigits() {
    var digits := "0123456789";
    expect forall i :: 52 <= i <= 61 ==> IndexToChar(i) in digits;
  }

  method {:test} TestIndexToCharLowercase() {
    var lowercase := "abcdefghijklmnopqrstuvwxyz";
    expect forall i :: 26 <= i <= 51 ==> IndexToChar(i) in lowercase;
  }

  method {:test} TestIndexToCharUppercase() {
    var uppercase := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    expect forall i :: 0 <= i <= 25 ==> IndexToChar(i) in uppercase;
  }

  method {:test} TestCharToIndex63() {
    expect CharToIndex('/') == 63;
  }

  method {:test} TestCharToIndex62() {
    expect CharToIndex('+') == 62;
  }

  method {:test} TestCharToIndexDigits() {
    var digits := "0123456789";
    expect forall i :: 0 <= i < |digits| ==> CharToIndex(digits[i]) == ((i + 52) as index);
  }

  method {:test} TestCharToIndexLowercase() {
    var lowercase := "abcdefghijklmnopqrstuvwxyz";
    expect forall i :: 0 <= i < |lowercase| ==> CharToIndex(lowercase[i]) == ((i + 26) as index);
  }

  method {:test} TestCharToIndexUppercase() {
    var uppercase := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    expect forall i :: 0 <= i < |uppercase| ==> CharToIndex(uppercase[i]) == (i as index);
  }

  method {:test} TestUInt24ToSeq() {
    var input: uint24 := 0x100101;
    var output := [0x10, 0x01, 0x01];
    expect output == UInt24ToSeq(input);
  }

  method {:test} TestSeqToUInt24() {
    var input := [0x10, 0x01, 0x01];
    var output: uint24 := 0x100101;
    expect output == SeqToUInt24(input);
  }

  method {:test} TestUInt24ToIndexSeq() {
    var input: uint24 := 0x100101;
    var output := [0x04, 0x00, 0x04, 0x01];
    expect output == UInt24ToIndexSeq(input);
  }

  method {:test} TestIndexSeqToUInt24() {
    var input := [0x04, 0x00, 0x04, 0x01];
    var output: uint24 := 0x100101;
    expect output == IndexSeqToUInt24(input);
  }

  method {:test} TestDecodeBlock() {
    var input := [0x04, 0x00, 0x04, 0x01];
    var output := [0x10, 0x01, 0x01];
    expect output == DecodeBlock(input);
  }

  method {:test} TestEncodeBlock() {
    var input := [0x10, 0x01, 0x01];
    var output := [0x04, 0x00, 0x04, 0x01];
    expect output == EncodeBlock(input);
  }

  method {:test} TestDecodeRecursively() {
    var input := [0x04, 0x00, 0x04, 0x01, 0x04, 0x00, 0x04, 0x01];
    var output := [0x10, 0x01, 0x01, 0x10, 0x01, 0x01];
    expect output == DecodeRecursively(input);
  }

  method {:test} TestEncodeRecursively() {
    var input := [0x10, 0x01, 0x01, 0x10, 0x01, 0x01];
    var output := [0x04, 0x00, 0x04, 0x01, 0x04, 0x00, 0x04, 0x01];
    expect output == EncodeRecursively(input);
  }

  method {:test} TestFromCharsToIndices() {
    var input := "aA1+/";
    var output := [0x1A, 0x00, 0x35, 0x3E, 0x3F];
    expect output == FromCharsToIndices(input);
  }

  method {:test} TestFromIndicesToChars() {
    var input := [0x1A, 0x00, 0x35, 0x3E, 0x3F];
    var output := "aA1+/";
    expect output == FromIndicesToChars(input);
  }

  method {:test} TestDecodeUnpadded() {
    var input := "VGVzdGluZysx";
    var output := [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E, 0x67, 0x2B, 0x31];
    expect output == DecodeUnpadded(input);
  }

  method {:test} TestEncodeUnpadded() {
    var input := [0x54, 0x65, 0x73, 0x74, 0x69, 0x6E, 0x67, 0x2B, 0x31];
    var output := "VGVzdGluZysx";
    expect output == EncodeUnpadded(input);
  }

  method {:test} TestDecodeUnpaddedEmpty() {
    expect [] == DecodeUnpadded([]);
  }

  method {:test} TestEncodeUnpaddedEmpty() {
    expect [] == EncodeUnpadded([]);
  }

  method {:test} TestIs1PaddingSuccess() {
    expect Is1Padding("VGU=");
  }

  method {:test} TestIs1PaddingTooShort() {
    expect !Is1Padding("VG=");
  }

  method {:test} TestIs1PaddingTooLong() {
    expect !Is1Padding("VGUU=");
  }

  method {:test} TestIs1PaddingInvalidChar0() {
    expect !Is1Padding("$GU=");
  }

  method {:test} TestIs1PaddingInvalidChar1() {
    expect !Is1Padding("V$U=");
  }

  method {:test} TestIs1PaddingInvalidChar2() {
    expect !Is1Padding("VG$=");
  }

  method {:test} TestIs1PaddingInvalidChar3() {
    expect !Is1Padding("VGVz");
  }

  method {:test} TestIs1PaddingInvalidChar2Modulus() {
    expect !Is1Padding("VGV=");
  }

  method {:test} TestDecode1Padding() {
    var input := "VGU=";
    var output := [0x54, 0x65];
    expect output == Decode1Padding(input);
  }

  method {:test} TestEncode1Padding() {
    var input := [0x54, 0x65];
    var output := "VGU=";
    expect output == Encode1Padding(input);
  }

  method {:test} TestIs2PaddingSuccess() {
    expect Is2Padding("VA==");
  }

  method {:test} TestIs2PaddingTooShort() {
    expect !Is2Padding("VA=");
  }

  method {:test} TestIs2PaddingTooLong() {
    expect !Is2Padding("VAA==");
  }

  method {:test} TestIs2PaddingInvalidChar0() {
    expect !Is2Padding("$A==");
  }

  method {:test} TestIs2PaddingInvalidChar1() {
    expect !Is2Padding("V$==");
  }

  method {:test} TestIs2PaddingInvalidChar2() {
    expect !Is2Padding("VAA=");
  }

  method {:test} TestIs2PaddingInvalidChar3() {
    expect !Is2Padding("VA=A");
  }

  method {:test} TestIs2PaddingInvalidChar1Modulus() {
    expect !Is2Padding("VB==");
  }

  method {:test} TestDecode2Padding() {
    var input := "VA==";
    var output := [0x54];
    expect output == Decode2Padding(input);
  }

  method {:test} TestEncode2Padding() {
    var input := [0x54];
    var output := "VA==";
    expect output == Encode2Padding(input);
  }

  method {:test} TestIsBase64StringTestVectors() {
    expect forall i :: i in BASE64_TEST_VECTORS_ENCODED ==> IsBase64String(i) == true;
  }

  method {:test} TestIsBase64StringBadLength() {
    expect !IsBase64String("VG=");
  }

  method {:test} TestIsBase64StringBadString() {
    expect !IsBase64String("VC==");
  }

  method {:test} TestSanityCheckDecodedTestVectors() {

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
      expect BASE64_TEST_VECTORS_DECODED_UINT8[testVectorIndex] == uint8Message;
      testVectorIndex := testVectorIndex + 1;
    }
  }

  method {:test} TestDecodeValidTestVectors() {
    expect forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      DecodeValid(BASE64_TEST_VECTORS_ENCODED[i]) == BASE64_TEST_VECTORS_DECODED_UINT8[i];
  }

  method {:test} TestDecodeTestVectors() {
    expect forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      Decode(BASE64_TEST_VECTORS_ENCODED[i]) == Success(BASE64_TEST_VECTORS_DECODED_UINT8[i]);
  }

  method {:test} TestDecodeFailure() {
    expect Failure("The encoding is malformed") == Decode("$");
  }

  method {:test} TestEncode() {
    expect forall i :: 0 <= i < |BASE64_TEST_VECTORS_DECODED_UINT8| ==>
      Encode(BASE64_TEST_VECTORS_DECODED_UINT8[i]) == BASE64_TEST_VECTORS_ENCODED[i];
  }

  method {:test} TestEncodeDecode() {
    expect forall i :: 0 <= i < |BASE64_TEST_VECTORS_DECODED_UINT8| ==>
      Decode(Encode(BASE64_TEST_VECTORS_DECODED_UINT8[i])) == Success(BASE64_TEST_VECTORS_DECODED_UINT8[i]);
  }

  method {:test} TestDecodeEncode() {
    expect forall i :: 0 <= i < |BASE64_TEST_VECTORS_ENCODED| ==>
      (Decode(BASE64_TEST_VECTORS_ENCODED[i]).Success?
      && Encode(Decode(BASE64_TEST_VECTORS_ENCODED[i]).value) == BASE64_TEST_VECTORS_ENCODED[i]);
  }
}
