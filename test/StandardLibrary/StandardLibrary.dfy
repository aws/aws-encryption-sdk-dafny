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
}
