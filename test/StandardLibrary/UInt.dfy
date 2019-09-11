// RUN: %dafny "./UInt.dfy" /compile:3 > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/UInt.dfy"

module TestUInt {
  import StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method TestSeqToUInt32() {
    var s := [0x01, 0x02, 0x30, 0x44];
    if SeqToUInt32(s) == 0x01023044 as uint32 {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestUInt32ToSeq() {
    var x := 0x01023044;
    if UInt32ToSeq(x) == [0x01, 0x02, 0x30, 0x44] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestSeqToUInt16() {
    var s := [0x01, 0x22];
    if SeqToUInt16(s) == 0x0122 as uint16 {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method TestUInt16ToSeq() {
    var x := 0x0122;
    if UInt16ToSeq(x) == [0x01, 0x22] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    TestSeqToUInt32();
    TestUInt32ToSeq();

    TestSeqToUInt16();
    TestUInt16ToSeq();
  }
}
