module {:extern "STLUInt"} StandardLibrary.UInt {
  const UINT8_LIMIT := 0x100
  newtype UInt8 = x | 0 <= x < UINT8_LIMIT

  const UINT16_LIMIT := 0x1_0000
  newtype UInt16 = x | 0 <= x < UINT16_LIMIT

  newtype Int32 = x | -0x8000_0000 <= x < 0x8000_0000

  const UINT32_LIMIT := 0x1_0000_0000
  newtype UInt32 = x | 0 <= x < UINT32_LIMIT

  newtype UInt64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  function method UInt16ToSeq(x: UInt16): seq<UInt8>
    ensures |UInt16ToSeq(x)| == 2
  {
    var b0: UInt8 := (x / 0x100) as UInt8;
    var b1: UInt8 := (x % 0x100) as UInt8;
    [b0, b1]
  }

  function method SeqToUInt16(p: seq<UInt8>): UInt16
    requires |p| == 2
  {
    var x0 := (p[0] as int) * 0x100;
    assert x0 <= UINT8_LIMIT * 0x100;
    var x := x0 + (p[1] as int);
    assert x < UINT16_LIMIT;
    x as UInt16
  }

  lemma UInt16SeqSerDeser(x: UInt16)
    ensures SeqToUInt16(UInt16ToSeq(x)) == x
  {}

  lemma UInt16SeqDeserSer(s: seq<UInt8>)
    requires |s| == 2
    ensures UInt16ToSeq(SeqToUInt16(s)) == s
  {}

  method UInt16ToArray(x: UInt16) returns (ret: array<UInt8>)
    ensures fresh(ret)
    ensures UInt16ToSeq(x) == ret[..]
    ensures ret.Length == 2
  {
    ret := new UInt8[2];
    ret[0] := (x / 0x100) as UInt8;
    ret[1] := (x % 0x100) as UInt8;
  }

  function method arrayToUInt16(p: array<UInt8>): (ret: UInt16)
    reads p
    requires p.Length == 2
    ensures SeqToUInt16(p[..]) == ret
  {
    var x0 := p[0] as int * 0x100;
    assert x0 <= 0x100 * 0x100;
    var x := x0 + p[1] as int;
    assert x < UINT16_LIMIT;
    x as UInt16
  }

  function method UInt32ToSeq(x: UInt32): seq<UInt8>
    ensures |UInt32ToSeq(x)| == 4
  {
    var b0 := ( x / 0x100_0000) as UInt8;
    var x0: UInt32 := x - (b0 as UInt32 * 0x100_0000);

    var b1 := (x0 / 0x1_0000) as UInt8;
    var x1: UInt32 := x0 - (b1 as UInt32 * 0x1_0000);

    var b2 := (x1 / 0x100) as UInt8;

    var b3 := (x1 % 0x100) as UInt8;
    [b0, b1, b2, b3]
  }

  function method SeqToUInt32(p: seq<UInt8>): UInt32
    requires |p| == 4
  {
    var x0 := p[0] as int * 0x100_0000;
    var x1 := x0 + p[1] as int * 0x1_0000;
    var x2 := x1 + p[2] as int * 0x100;
    var x := x2 + p[3] as int;
    assert x < UINT32_LIMIT;
    x as UInt32
  }

  lemma UInt32SeqSerDeser(x: UInt32)
    ensures SeqToUInt32(UInt32ToSeq(x)) == x
  {}

  lemma UInt32SeqDeserSer(s: seq<UInt8>)
    requires |s| == 4
    ensures UInt32ToSeq(SeqToUInt32(s)) == s
  {}

  method UInt32ToArray(x: UInt32) returns (ret: array<UInt8>)
    ensures fresh(ret)
    ensures UInt32ToSeq(x) == ret[..]
    ensures ret.Length == 4
  {
    var x' := x;
    ret := new UInt8[4];

    ret[0] := (x' / 0x100_0000) as UInt8;
    x' := x' - (ret[0] as UInt32 * 0x100_0000);

    ret[1] := (x' / 0x1_0000) as UInt8;
    x' := x' - (ret[1] as UInt32 * 0x1_0000);

    ret[2] := (x' / 0x100) as UInt8;

    ret[3] := (x' % 0x100) as UInt8;
  }

  function method ArrayToUInt32(p: array<UInt8>): (ret: UInt32)
    reads p
    requires p.Length == 4
    ensures SeqToUInt32(p[..]) == ret
  {
    var x0 := p[0] as int * 0x100_0000;
    var x1 := x0 + p[1] as int * 0x1_0000;
    var x2 := x1 + p[2] as int * 0x100;
    var x := x2 + p[3] as int;
    assert x < UINT32_LIMIT;
    x as UInt32
  }
}
