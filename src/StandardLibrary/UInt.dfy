module {:extern "STLUInt"} StandardLibrary.UInt {
  newtype uint8 = x | 0 <= x < 0x100

  const UINT16_LIMIT := 0x1_0000
  newtype uint16 = x | 0 <= x < 0x1_0000

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  newtype uint32 = x | 0 <= x < 0x1_0000_0000

  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  function method UInt16ToSeq(x: uint16): seq<uint8>
    ensures |UInt16ToSeq(x)| == 2
  {
    var b0: uint8 := (x / 0x100) as uint8;
    var b1: uint8 := (x % 0x100) as uint8;
    [b0, b1]
  }

  function method SeqToUInt16(s: seq<uint8>): uint16
    requires |s| == 2
  {
    var x0 := s[0] as int * 0x100;
    var x := x0 + s[1] as int;
    x as uint16
  }

  lemma UInt16SeqSerDeser(x: uint16)
    ensures SeqToUInt16(UInt16ToSeq(x)) == x
  {}

  lemma UInt16SeqDeserSer(s: seq<uint8>)
    requires |s| == 2
    ensures UInt16ToSeq(SeqToUInt16(s)) == s
  {}

  method UInt16ToArray(x: uint16) returns (ret: array<uint8>)
    ensures fresh(ret)
    ensures UInt16ToSeq(x) == ret[..]
    ensures ret.Length == 2
  {
    ret := new uint8[2];
    ret[0] := (x / 0x100) as uint8;
    ret[1] := (x % 0x100) as uint8;
  }

  function method ArrayToUInt16(a: array<uint8>): (ret: uint16)
    reads a
    requires a.Length == 2
    ensures SeqToUInt16(a[..]) == ret
  {
    var x0 := a[0] as int * 0x100;
    var x := x0 + a[1] as int;
    x as uint16
  }

  function method UInt32ToSeq(x: uint32): seq<uint8>
    ensures |UInt32ToSeq(x)| == 4
  {
    var b0 := ( x / 0x100_0000) as uint8;
    var x0: uint32 := x - (b0 as uint32 * 0x100_0000);

    var b1 := (x0 / 0x1_0000) as uint8;
    var x1: uint32 := x0 - (b1 as uint32 * 0x1_0000);

    var b2 := (x1 / 0x100) as uint8;

    var b3 := (x1 % 0x100) as uint8;
    [b0, b1, b2, b3]
  }

  function method SeqToUInt32(s: seq<uint8>): uint32
    requires |s| == 4
  {
    var x0 := s[0] as int * 0x100_0000;
    var x1 := x0 + s[1] as int * 0x1_0000;
    var x2 := x1 + s[2] as int * 0x100;
    var x := x2 + s[3] as int;
    x as uint32
  }

  lemma UInt32SeqSerDeser(x: uint32)
    ensures SeqToUInt32(UInt32ToSeq(x)) == x
  {}

  lemma UInt32SeqDeserSer(s: seq<uint8>)
    requires |s| == 4
    ensures UInt32ToSeq(SeqToUInt32(s)) == s
  {}

  method UInt32ToArray(x: uint32) returns (ret: array<uint8>)
    ensures fresh(ret)
    ensures UInt32ToSeq(x) == ret[..]
    ensures ret.Length == 4
  {
    var x' := x;
    ret := new uint8[4];

    ret[0] := (x' / 0x100_0000) as uint8;
    x' := x' - (ret[0] as uint32 * 0x100_0000);

    ret[1] := (x' / 0x1_0000) as uint8;
    x' := x' - (ret[1] as uint32 * 0x1_0000);

    ret[2] := (x' / 0x100) as uint8;

    ret[3] := (x' % 0x100) as uint8;
  }

  function method ArrayToUInt32(a: array<uint8>): (ret: uint32)
    reads a
    requires a.Length == 4
    ensures SeqToUInt32(a[..]) == ret
  {
    var x0 := a[0] as int * 0x100_0000;
    var x1 := x0 + a[1] as int * 0x1_0000;
    var x2 := x1 + a[2] as int * 0x100;
    var x := x2 + a[3] as int;
    x as uint32
  }
}
