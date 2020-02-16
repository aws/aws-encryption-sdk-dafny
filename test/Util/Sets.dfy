include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Util/Sets.dfy"

module TestSeqReaderReadElements {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Sets

  method {:test} TestSetToOrderedSequenceEmpty() returns (r: Result<()>) {
    var output := ComputeSetToOrderedSequence({}, UInt8Less);
    var expected := [];
    r := RequireEqual(output, expected);
  }

  method {:test} TestSetToOrderedSequenceOneItem() returns (r: Result<()>) {
    var a := {[0]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0]];
    r := RequireEqual(output, expected);
  }

  method {:test} TestSetToOrderedSequenceSimple() returns (r: Result<()>) {
    var a := {[0, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 2]];
    r := RequireEqual(output, expected);
  }

  method {:test} TestSetToOrderedSequencePrefix() returns (r: Result<()>) {
    var a := {[0, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2]];
    r := RequireEqual(output, expected);
  }

  method {:test} TestSetToOrderedSequenceComplex() returns (r: Result<()>) {
    var a := {[0, 1, 2], [1, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2], [1, 1, 2]];
    r := RequireEqual(output, expected);
  }

  method {:test} TestSetToOrderedSequenceManyItems() returns (r: Result<()>) {
    var a := set x:uint16 | 0 <= x < 0xFFFF :: UInt16ToSeq(x);
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected : seq<seq<uint8>> := seq(0xFFFF, i requires 0 <= i < 0xFFFF => UInt16ToSeq(i as uint16));
    r := RequireEqual(output, expected);
  }

}
