include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestStandardLibrary {
  import opened StandardLibrary

  method {:test} TestJoinMultiElementSeq() returns (ret: Result<()>) {
    var input := ["comma", "separated", "list"];
    var output := Join(input, ",");
    ret := RequireEqual("comma,separated,list", output);
  }

  method {:test} TestJoinSingleElementSeq() returns (ret: Result<()>) {
    var input := ["one"];
    var output := Join(input, ",");
    ret := RequireEqual("one", output);
  }

  method {:test} TestJoinSplit() returns (ret: Result<()>) {
    var input := "comma,separated,list";
    var output := Join(Split(input, ','), ",");
    ret := RequireEqual(input, output);
  }

  method {:test} TestSplitJoin() returns (ret: Result<()>) {
    var input := ["comma", "separated", "list"];
    var output := Split(Join(input, ","), ',');
    ret := RequireEqual(input, output);
  }

  method {:test} TestSplitByteSeq() returns (ret: Result<()>) {
    var input := "comma,separated,list";
    var output := Split(input, ',');
    ret := RequireEqual(["comma", "separated", "list"], output);
  }

  method {:test} TestSplitNumSeq() returns (ret: Result<()>) {
    var input := [1, 2, 3, 0, 1, 2, 3];
    var output := Split(input, 0);
    ret := RequireEqual([[1, 2, 3], [1, 2, 3]], output);
  }

  method {:test} TestSplitFinalElementDelim() returns (ret: Result<()>) {
    var input := "one,";
    var output := Split(input, ',');
    ret := RequireEqual(["one", ""], output);
  }

  method {:test} TestSplitNoDelim() returns (ret: Result<()>) {
    var input := "no comma";
    var output := Split(input, ',');
    ret := RequireEqual(["no comma"], output);
  }

  method {:test} TestSplitOnlyElemIsDelim() returns (ret: Result<()>) {
    var input := ",";
    var output := Split(input, ',');
    ret := RequireEqual(["", ""], output);
  }

  method {:test} TestSplitEmpty() returns (ret: Result<()>) {
    var input := "";
    var output := Split(input, ',');
    ret := RequireEqual([""], output);
  }

    method {:test} TestFindSimple() returns (ret: Result<()>) {
    var input := "abcd";
    var output := Find(input, 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindDuplicates() returns (ret: Result<()>) {
    var input := "abcdc";
    var output := Find(input, 'c', 0);
    ret := RequireEqual(Some(2), output);
  }

  method {:test} TestFindNone() returns (ret: Result<()>) {
    var input := "abcd";
    var output := Find(input, 'e', 0);
    ret := RequireEqual(None, output);
  }

  predicate method TestFilterPredicate(entry: seq<char>) {
    entry in ["a"]
  }

  method {:test} TestFilterSomeValid() returns (ret: Result<()>) {
    var input := ["a", "b", "a"];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual(["a", "a"], output);
  }

  method {:test} TestFilterNomneValid() returns (ret: Result<()>) {
    var input := ["c", "b", "c"];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual([], output);
  }

  method {:test} TestFilterNothing() returns (ret: Result<()>) {
    var input := [];
    var output := Filter(input, TestFilterPredicate);
    ret := RequireEqual([], output);
  }

  method {:test} TestFill() returns (ret: Result<()>) {
    var input := "a";
    var output := Fill(input, 5);
    ret := RequireEqual(["a","a","a", "a", "a"], output);
  }

  method {:test} TestFillNothing() returns (ret: Result<()>) {
    var input := "a";
    var output := Fill(input, 0);
    ret := RequireEqual([], output);
  }

  method {:test} TestMinPositives() returns (ret: Result<()>) {
    ret := RequireEqual(1, Min(1, 2));
  }

  method {:test} TestMinNegatives() returns (ret: Result<()>) {
    ret := RequireEqual(-2, Min(-1, -2));
  }

  method {:test} TestMinPositivesNegatives() returns (ret: Result<()>) {
    ret := RequireEqual(-1, Min(-1, 1));
  }

  method {:test} TestMinDuplicateNumber() returns (ret: Result<()>) {
    ret := RequireEqual(0, Min(0, 0));
  }

  method {:test} TestSeqToArray() returns (ret: Result<()>) {
    var input: seq<int> := [1, 2, 3];
    var output := SeqToArray(input);

    var expected := new int[3];
    expected[0] := 1;
    expected[1] := 2;
    expected[2] := 3;

    var allResults: seq<Result<()>> := [];
    allResults := allResults + [RequireEqual(expected.Length, output.Length)];
    allResults := allResults + [RequireEqual(expected[0], output[0])];
    allResults := allResults + [RequireEqual(expected[1], output[1])];
    allResults := allResults + [RequireEqual(expected[2], output[2])];
    ret := Require(|allResults| == 4 && forall result :: result in allResults ==> result.Success?);
  }

  method {:test} TestSeqToArrayEmpty() returns (ret: Result<()>) {
    var input: seq<char> := [];
    var output := SeqToArray(input);
    ret := RequireEqual(0, output.Length);
  }
}
