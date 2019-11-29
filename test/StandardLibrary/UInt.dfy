include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"

module {:extern "TestUInt"} TestUInt  {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  function method {:test} TestSeqToUInt32(): Result<()> {
    var s := [0x01, 0x02, 0x30, 0x44];
    RequireEqual(0x01023044 as uint32, SeqToUInt32(s))
  }

  function method {:test} TestUInt32ToSeq(): Result<()> {
    var x := 0x01023044;
    RequireEqual([0x01, 0x02, 0x30, 0x44], UInt32ToSeq(x))
  }

  function method {:test} TestSeqToUInt16(): Result<()> {
    var s := [0x01, 0x22];
    RequireEqual(0x0122 as uint16, SeqToUInt16(s))
  }

  function method {:test} TestUInt16ToSeq(): Result<()> {
    var x := 0x0122;
    RequireEqual([0x01, 0x22], UInt16ToSeq(x))
  }
}
