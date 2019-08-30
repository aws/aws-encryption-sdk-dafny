module {:extern "STLUINT"} StandardLibrary.UInt {
    newtype uint8 = x | 0 <= x < 256

    newtype uint16 = x | 0 <= x < 0x1_0000
    const UINT16_MAX := 0x1_0000 - 1

    newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

    newtype uint32 = x | 0 <= x < 0x1_0000_0000
    const UINT32_MAX := 0x1_0000_0000 - 1

    newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

    function method uint16ToSeq(x: uint16): seq<uint8>
        ensures |uint16ToSeq(x)| == 2
    {
        var b0: uint8 := (x / 256) as uint8;
        var b1: uint8 := (x % 256) as uint8;
        [b0, b1]
    }

    function method seqToUInt16(p: seq<uint8>): uint16 
        requires |p| == 2
    {
        var x1 :=      (p[0] as int) * 256;
        assert x1 <= 256 * 256;
        var  x := x1 + (p[1] as int);
        assert x <= UINT16_MAX;
        x as uint16
    }

    lemma uint16SeqSerDeser(x: uint16)
        ensures seqToUInt16(uint16ToSeq(x)) == x
    {}

    lemma uint16SeqDeserSer(s: seq<uint8>)
        requires |s| == 2
        ensures uint16ToSeq(seqToUInt16(s)) == s
    {}

    method uint16ToArray(x: uint16) returns (ret: array<uint8>)
        ensures fresh(ret)
        ensures uint16ToSeq(x) == ret[..]
        ensures ret.Length == 2
    {
        ret := new uint8[2];
        ret[0] := (x / 256) as uint8;
        ret[1] := (x % 256) as uint8;
    }
    
    function method arrayToUInt16(p: array<uint8>): (ret: uint16)
        reads p
        requires p.Length == 2
        ensures seqToUInt16(p[..]) == ret
    {
        var x1 :=      p[0] as int * 256;
        assert x1 <= 256 * 256;
        var  x := x1 + p[1] as int;
        assert x <= UINT16_MAX;
        x as uint16
    }

    function method uint32ToSeq(x: uint32): seq<uint8>
        ensures |uint32ToSeq(x)| == 4
    {
        var b0 := ( x / 0x100_0000) as uint8;
        var x0: uint32 :=  x - (b0 as uint32 * 0x100_0000);

        var b1 := (x0 / 0x1_0000) as uint8;
        var x1: uint32 := x0 - (b1 as uint32 * 0x1_0000);

        var b2 := (x1 / 0x100) as uint8;
        // or for symmetry:
        // x2 := x1 - (b2 * 0x100);
        // b3 := (x2 / 1) as uint8;
        var b3 := (x1 % 0x100) as uint8;
        [b0, b1, b2, b3]
    }

    function method seqToUInt32(p: seq<uint8>): uint32
        requires |p| == 4
    {
        // 2^24 = 0x100_0000
        var x3 :=      p[0] as int * 0x100_0000;
        // 2^16 = 0x1_0000
        var x2 := x3 + p[1] as int * 0x1_0000;
        // 2^8 = 0x100
        var x1 := x2 + p[2] as int * 0x100;
        // 2^0 = 0x1
        var  x := x1 + p[3] as int;
        assert x <= UINT32_MAX;
        x as uint32
    }

    lemma uint32SeqSerDeser(x: uint32)
        ensures seqToUInt32(uint32ToSeq(x)) == x
    {}

    lemma uint32SeqDeserSer(s: seq<uint8>)
        requires |s| == 4
        ensures uint32ToSeq(seqToUInt32(s)) == s
    {}

    method uint32ToArray(x: uint32) returns (ret: array<uint8>)
        ensures fresh(ret)
        ensures uint32ToSeq(x) == ret[..]
        ensures ret.Length == 4
    {
        var x' := x;
        ret := new uint8[4];

        ret[0] := (x' / 0x100_0000) as uint8;
        x' := x' - (ret[0] as uint32 * 0x100_0000);

        ret[1] := (x' / 0x1_0000) as uint8;
        x' := x' - (ret[1] as uint32 * 0x1_0000);

        ret[2] := (x' / 0x100) as uint8;
        // or for symmetry:
        // x' := x' - (ret[2] * 0x100);
        // ret[3] := (x' / 1) as uint8;
        ret[3] := (x' % 0x100) as uint8;
    }

    function method arrayToUInt32(p: array<uint8>): (ret: uint32)
        reads p
        requires p.Length == 4
        ensures seqToUInt32(p[..]) == ret
    {
        // 2^24 = 0x100_0000
        var x3 :=      p[0] as int * 0x100_0000;
        // 2^16 = 0x1_0000
        var x2 := x3 + p[1] as int * 0x1_0000;
        // 2^8 = 0x100
        var x1 := x2 + p[2] as int * 0x100;
        // 2^0 = 0x1
        var  x := x1 + p[3] as int;
        assert x <= UINT32_MAX;
        x as uint32
    }
}
>>>>>>> d86c7da4676e9cfc8609dd5cb492177e18867845
