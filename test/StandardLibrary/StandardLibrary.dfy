include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestStdLib {
  import opened StandardLibrary

  function method {:test} TestSplit0(): Result<()> {
    var input := "Comma,seperated,list";
    var output := Split(input, ',');
    RequireEqual(["Comma", "seperated", "list"], output)
  }

  function method {:test} TestSplit1(): Result<()> {
    var input := [1,2,3,0,1,2,3];
    var output := Split(input, 0);
    RequireEqual([[1,2,3], [1,2,3]], output)
  }

  function method {:test} TestSplit2(): Result<()> {
    var input := "one,";
    var output := Split(input, ',');
    RequireEqual(["one", ""], output)
  }

  function method {:test} TestSplit3(): Result<()> {
    var input := "no comma";
    var output := Split(input, ',');
    RequireEqual(["no comma"], output)
  }

  function method {:test} TestSplit4(): Result<()> {
    var input := "";
    var output := Split(input, ',');
    RequireEqual([""], output)
  }

  function method {:test} TestJoin0(): Result<()> {
    var input := ["Comma", "seperated", "list"];
    var output := Join(input, ",");
    RequireEqual("Comma,seperated,list", output)
  }

  function method {:test} TestJoin1(): Result<()> {
    var input := ["one"];
    var output := Join(input, ",");
    RequireEqual("one", output)
  }

  function method {:test} TestSplitJoin(): Result<()> {
    var input := "Comma,seperated,list";
    var output := Join(Split(input, ','), ",");
    RequireEqual(input, output)
  }

  function method {:test} TestJoinSplit(): Result<()> {
    var input := ["Comma", "seperated", "list"];
    var output := Split(Join(input, ","), ',');
    RequireEqual(input, output)
  }
}
