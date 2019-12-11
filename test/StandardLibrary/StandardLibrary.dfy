// RUN: %dafny %s /compile:3 > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestStdLib {
  import opened StandardLibrary

  method TestSplit0() {
    var input := "Comma,seperated,list";
    var output := Split(input, ',');
    if output == ["Comma", "seperated", "list"] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestSplit1() {
    var input := [1,2,3,0,1,2,3];
    var output := Split(input, 0);
    if output == [[1,2,3], [1,2,3]] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestSplit2() {
    var input := "one,";
    var output := Split(input, ',');
    if output == ["one", ""] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestSplit3() {
    var input := "no comma";
    var output := Split(input, ',');
    if output == ["no comma"] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestSplit4() {
    var input := "";
    var output := Split(input, ',');
    if output == [""] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestJoin0() {
    var input := ["Comma", "seperated", "list"];
    var output := Join(input, ",");
    if output == "Comma,seperated,list" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestJoin1() {
    var input := ["one"];
    var output := Join(input, ",");
    if output == "one" {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestSplitJoin() {
    var input := "Comma,seperated,list";
    var output := Join(Split(input, ','), ",");
    if output == input {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method TestJoinSplit() {
    var input := ["Comma", "seperated", "list"];
    var output := Split(Join(input, ","), ',');
    if output == input {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
      print output;
    }
  }

  method Main() {
    TestSplit0();
    TestSplit1();
    TestSplit2();
    TestSplit3();
    TestSplit4();

    TestJoin0();
    TestJoin1();

    TestSplitJoin();
    TestJoinSplit();
  }
}
