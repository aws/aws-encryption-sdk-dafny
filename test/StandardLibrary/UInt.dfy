// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"

module TestUInt {
  import opened UInt = StandardLibrary.UInt

  method {:test} TestUInt16ToSeq() {
    var x: uint16 := 0x0122;
    expect [0x01, 0x22] == UInt16ToSeq(x);
  }

  method {:test} TestSeqToUInt16() {
    var s := [0x01, 0x22];
    expect 0x0122 as uint16 == SeqToUInt16(s);
  }

  method {:test} TestUInt32ToSeq() {
    var x := 0x01023044;
    expect [0x01, 0x02, 0x30, 0x44] == UInt32ToSeq(x);
  }

  method {:test} TestSeqToUInt32() {
    var s := [0x01, 0x02, 0x30, 0x44];
    expect 0x01023044 as uint32 == SeqToUInt32(s);
  }

  method {:test} TestUInt64ToSeq() {
    var x: uint64 := 0x0102304455667788;
    expect [0x01, 0x02, 0x30, 0x44, 0x55, 0x66, 0x77, 0x88] == UInt64ToSeq(x);
  }

  method {:test} TestSeqToUInt64() {
    var s := [0x01, 0x02, 0x30, 0x44, 0x55, 0x66, 0x77, 0x88];
    expect 0x0102304455667788 as uint64 == SeqToUInt64(s);
  }
}
