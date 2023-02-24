// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Sets.dfy"

module TestSeqReaderReadElements {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened SortedSets

  method {:test} TestSetToOrderedSequenceEmpty() {
    var output := ComputeSetToOrderedSequence({}, UInt8Less);
    var expected := [];
    expect output == expected;
  }

  method {:test} TestSetToOrderedSequenceOneItem() {
    var a := {[0]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0]];
    expect output == expected;
  }

  method {:test} TestSetToOrderedSequenceSimple() {
    var a := {[0, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 2]];
    expect output == expected;
  }

  method {:test} TestSetToOrderedSequencePrefix() {
    var a := {[0, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2]];
    expect output == expected;
  }

  method {:test} TestSetToOrderedSequenceComplex() {
    var a := {[0, 1, 2], [1, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2], [1, 1, 2]];
    expect output == expected;
  }

  method {:test} TestSetToOrderedSequenceManyItems() {
    var a := set x:uint16 | 0 <= x < 0xFFFF :: UInt16ToSeq(x);
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected : seq<seq<uint8>> := seq(0xFFFF, i requires 0 <= i < 0xFFFF => UInt16ToSeq(i as uint16));
    expect output == expected;
  }

}
