include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestStandardLibrary {
  import opened StandardLibrary

  method {:test} TestRequireFailure() returns (ret: TestResult) {
    var failure: Result<string> := Failure("Some failure");
    :- RequireFailure(failure);

    var requireFailureGivenSuccess := RequireFailure(Success(()));
    :- Require(requireFailureGivenSuccess.TestFailure?);
    ret := RequireFailure<()>(Failure(requireFailureGivenSuccess.error));
  }

  method {:test} TestJoinMultiElementSeq() returns (ret: TestResult) {
    var input := ["comma", "separated", "list"];
    var output := Join(input, ",");
    ret := RequireEqual("comma,separated,list", output);
  }

  method {:test} TestJoinSingleElementSeq() returns (ret: TestResult) {
    var input := ["one"];
    var output := Join(input, ",");
    ret := RequireEqual("one", output);
  }

  method {:test} TestJoinSplit() returns (ret: TestResult) {
    var input := "comma,separated,list";
    var output := Join(Split(input, ','), ",");
    ret := RequireEqual(input, output);
  }

  method {:test} TestSplitJoin() returns (ret: TestResult) {
    var input := ["comma", "separated", "list"];
    var output := Split(Join(input, ","), ',');
    ret := RequireEqual(input, output);
  }

  method {:test} TestSplitByteSeq() returns (ret: TestResult) {
    var input := "comma,separated,list";
    var output := Split(input, ',');
    ret := RequireEqual(["comma", "separated", "list"], output);
  }

  method {:test} TestSplitNumSeq() returns (ret: TestResult) {
    var input := [1, 2, 3, 0, 1, 2, 3];
    var output := Split(input, 0);
    ret := RequireEqual([[1, 2, 3], [1, 2, 3]], output);
  }

  method {:test} TestSplitFinalElementDelim() returns (ret: TestResult) {
    var input := "one,";
    var output := Split(input, ',');
    ret := RequireEqual(["one", ""], output);
  }

  method {:test} TestSplitNoDelim() returns (ret: TestResult) {
    var input := "no comma";
    var output := Split(input, ',');
    ret := RequireEqual(["no comma"], output);
  }

  method {:test} TestSplitOnlyElemIsDelim() returns (ret: TestResult) {
    var input := ",";
    var output := Split(input, ',');
    ret := RequireEqual(["", ""], output);
  }

  method {:test} TestSplitEmpty() returns (ret: TestResult) {
    var input := "";
    var output := Split(input, ',');
    ret := RequireEqual([""], output);
  }

  method {:test} TestFindIndexMatchingSimple() returns (ret: TestResult) {
    var input := "abcd";
    var output := FindIndexMatching(input, 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindIndexMatchingDuplicates() returns (ret: TestResult) {
    var input := "abcdc";
    var output := FindIndexMatching(input, 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindIndexMatchingNone() returns (ret: TestResult) {
    var input := "abcd";
    var output := FindIndexMatching(input, 'e', 0);
    ret := RequireEqual(None, output);
  }

  method {:test} TestFindIndexSimple() returns (ret: TestResult)
  {
    var input := "abcd";
    var output := FindIndex(input, x => x == 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindIndexComplex() returns (ret: TestResult)
  {
    var input := "abcd";
    var output := FindIndex(input, x => x in "crepe", 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindIndexDuplicates() returns (ret: TestResult)
  {
    var input := "abcdc";
    var output := FindIndex(input, x => x == 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindIndexNone() returns (ret: TestResult)
  {
    var input := "abcd";
    var output := FindIndex(input, x => false, 0);
    ret := RequireEqual(None, output);
  }

  predicate method TestFilterPredicate(entry: seq<char>) {
    entry in ["a"]
  }

  method {:test} TestFilterSomeValid() returns (ret: TestResult) {
    var input := ["a", "b", "a"];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual(["a", "a"], output);
  }

  method {:test} TestFilterNoneValid() returns (ret: TestResult) {
    var input := ["c", "b", "c"];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual([], output);
  }

  method {:test} TestFilterNothing() returns (ret: TestResult) {
    var input := [];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual([], output);
  }

  method {:test} TestMinPositives() returns (ret: TestResult) {
    ret := RequireEqual(1, Min(1, 2));
  }

  method {:test} TestMinNegatives() returns (ret: TestResult) {
    ret := RequireEqual(-2, Min(-1, -2));
  }

  method {:test} TestMinPositivesNegatives() returns (ret: TestResult) {
    ret := RequireEqual(-1, Min(-1, 1));
  }

  method {:test} TestMinDuplicateNumber() returns (ret: TestResult) {
    ret := RequireEqual(0, Min(0, 0));
  }

  method {:test} TestSeqToArray() returns (ret: TestResult) {
    var input: seq<int> := [1, 2, 3];
    var output := SeqToArray(input);

    var expected := new int[3];
    expected[0] := 1;
    expected[1] := 2;
    expected[2] := 3;

    :- RequireEqual(expected.Length, output.Length);
    :- RequireEqual(expected[0], output[0]);
    :- RequireEqual(expected[1], output[1]);
    ret := RequireEqual(expected[2], output[2]);
  }

  method {:test} TestSeqToArrayEmpty() returns (ret: TestResult) {
    var input: seq<char> := [];
    var output := SeqToArray(input);
    ret := RequireEqual(0, output.Length);
  }

  predicate method TestStandardLibraryLessPredicate(a: int, b: int) { a < b }

  method {:test} TestLexicographicLessOrEqualTrue() returns (ret: TestResult) {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 4];
    ret := RequireEqual(true, LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate));
  }

  method {:test} TestLexicographicLessOrEqualFalse() returns (ret: TestResult) {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 4];
    ret := RequireEqual(false, LexicographicLessOrEqual(b, a, TestStandardLibraryLessPredicate));
  }

  method {:test} TestLexicographicLessOrEqualAllEqual() returns (ret: TestResult) {
    var a: seq<int> := [1, 2, 3];
    var b: seq<int> := [1, 2, 3];
    ret := RequireEqual(true, LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate));
  }

  method {:test} TestLexicographicLessOrEqualNoneEqual() returns (ret: TestResult) {
    var a: seq<int> := [1];
    var b: seq<int> := [2];
    ret := RequireEqual(true, LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate));
  }

  method {:test} TestLexicographicLessOrEqualEmpty() returns (ret: TestResult) {
    var a: seq<int> := [];
    var b: seq<int> := [];
    ret := RequireEqual(true, LexicographicLessOrEqual(a, b, TestStandardLibraryLessPredicate));
  }
}
