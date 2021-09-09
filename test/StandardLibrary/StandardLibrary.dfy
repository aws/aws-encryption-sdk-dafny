// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestStandardLibrary {
  import opened Wrappers
  import opened StandardLibrary

  method {:test} TestJoinMultiElementSeq() {
    var input := ["comma", "separated", "list"];
    var output := Join(input, ",");
    expect "comma,separated,list" == output;
  }

  method {:test} TestJoinSingleElementSeq() {
    var input := ["one"];
    var output := Join(input, ",");
    expect "one" == output;
  }

  method {:test} TestJoinSplit() {
    var input := "comma,separated,list";
    var output := Join(Split(input, ','), ",");
    expect input == output;
  }

  method {:test} TestSplitJoin() {
    var input := ["comma", "separated", "list"];
    var output := Split(Join(input, ","), ',');
    expect input == output;
  }

  method {:test} TestSplitByteSeq() {
    var input := "comma,separated,list";
    var output := Split(input, ',');
    expect ["comma", "separated", "list"] == output;
  }

  method {:test} TestSplitNumSeq() {
    var input := [1, 2, 3, 0, 1, 2, 3];
    var output := Split(input, 0);
    expect [[1, 2, 3], [1, 2, 3]] == output;
  }

  method {:test} TestSplitFinalElementDelim() {
    var input := "one,";
    var output := Split(input, ',');
    expect ["one", ""] == output;
  }

  method {:test} TestSplitNoDelim() {
    var input := "no comma";
    var output := Split(input, ',');
    expect ["no comma"] == output;
  }

  method {:test} TestSplitOnlyElemIsDelim() {
    var input := ",";
    var output := Split(input, ',');
    expect ["", ""] == output;
  }

  method {:test} TestSplitEmpty() {
    var input := "";
    var output := Split(input, ',');
    expect [""] == output;
  }

  method {:test} TestFindIndexMatchingSimple() {
    var input := "abcd";
    var output := FindIndexMatching(input, 'c', 0);
    expect Some(2) == output;
  }

  method {:test} TestFindIndexMatchingDuplicates() {
    var input := "abcdc";
    var output := FindIndexMatching(input, 'c', 0);
    expect Some(2) == output;
  }

  method {:test} TestFindIndexMatchingNone() {
    var input := "abcd";
    var output := FindIndexMatching(input, 'e', 0);
    expect None == output;
  }

  method {:test} TestFindIndexSimple()
  {
    var input := "abcd";
    var output := FindIndex(input, x => x == 'c', 0);
    expect Some(2) == output;
  }

  method {:test} TestFindIndexComplex()
  {
    var input := "abcd";
    var output := FindIndex(input, x => x in "crepe", 0);
    expect Some(2) == output;
  }

  method {:test} TestFindIndexDuplicates()
  {
    var input := "abcdc";
    var output := FindIndex(input, x => x == 'c', 0);
    expect Some(2) == output;
  }

  method {:test} TestFindIndexNone()
  {
    var input := "abcd";
    var output := FindIndex(input, x => false, 0);
    expect None == output;
  }

  predicate method TestFilterPredicate(entry: seq<char>) {
    entry in ["a"]
  }

  method {:test} TestFilterSomeValid() {
    var input := ["a", "b", "a"];
    var output := Filter(input, TestFilterPredicate);
    expect ["a", "a"] == output;
  }

  method {:test} TestFilterNoneValid() {
    var input := ["c", "b", "c"];
    var output := Filter(input, TestFilterPredicate);
    expect [] == output;
  }

  method {:test} TestFilterNothing() {
    var input := [];
    var output := Filter(input, TestFilterPredicate);
    expect [] == output;
  }

  method {:test} TestFillZero() {
    var output := Fill(0, 50);
    expect seq(50, _ => 0) == output;
  }

  method {:test} TestFillChars() {
    var output := Fill("a", 25);
    expect seq(25, _ => "a") == output;
  }

  method {:test} TestMinPositives() {
    expect 1 == Min(1, 2);
  }

  method {:test} TestMinNegatives() {
    expect -2 == Min(-1, -2);
  }

  method {:test} TestMinPositivesNegatives() {
    expect -1 == Min(-1, 1);
  }

  method {:test} TestMinDuplicateNumber() {
    expect 0 == Min(0, 0);
  }

  method {:test} TestSeqToArray() {
    var input: seq<int> := [1, 2, 3];
    var output := SeqToArray(input);

    // unless an initializer is provided for the array elements, a new array of 'int' must have empty size
    // fill with values to start (1, 2, 3)
    var expected := new int[3](i => i + 1);

    expect expected.Length == output.Length;
    expect expected[0] == output[0];
    expect expected[1] == output[1];
    expect expected[2] == output[2];
  }

  method {:test} TestSeqToArrayEmpty() {
    var input: seq<char> := [];
    var output := SeqToArray(input);
    expect 0 == output.Length;
  }

  predicate method TestStandardLibraryLessPredicate(a: int, b: int) { a < b }

  method {:test} TestLexicographicLessOrEqualTrue() {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 4];
    expect LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate);
  }

  method {:test} TestLexicographicLessOrEqualFalse() {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 4];
    expect !LexicographicLessOrEqual(b, a, TestStandardLibraryLessPredicate);
  }

  method {:test} TestLexicographicLessOrEqualAllEqual() {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 3];
    expect LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate);
  }

  method {:test} TestLexicographicLessOrEqualNoneEqual() {
    var a: seq<int> := [1];
    var b: seq<int> := [2];
    expect LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate);
  }

  method {:test} TestLexicographicLessOrEqualEmpty() {
    var a: seq<int> := [];
    var b: seq<int> := [];
    expect LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate);
  }
}
