// RUN: %dafny "./UInt.dfy" /compile:3 > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/UInt.dfy"

module TestUInt {
  import StandardLibrary
  import opened UInt = StandardLibrary.UInt

  method testSeqToUInt32() {
    var s := [0x01, 0x02, 0x30, 0x44];
    if seqToUInt32(s) == 0x01023044 as uint32 {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method testUInt32ToSeq() {
    var x := 0x01023044;
    if uint32ToSeq(x) == [0x01, 0x02, 0x30, 0x44] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method testSeqToUInt16() {
    var s := [0x01, 0x22];
    if seqToUInt16(s) == 0x0122 as uint16 {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method testUInt16ToSeq() {
    var x := 0x0122;
    if uint16ToSeq(x) == [0x01, 0x22] {
      print "CORRECT\n";
    } else {
      print "NOT CORRECT\n";
    }
  }

  method Main() {
    testSeqToUInt32();
    testUInt32ToSeq();

    testSeqToUInt16();
    testUInt16ToSeq();
  }
}