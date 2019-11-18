module {:extern "STLUInt"} StandardLibrary.UInt {
  newtype uint8 = x | 0 <= x < 0x100

  const UINT16_LIMIT := 0x1_0000
  newtype uint16 = x | 0 <= x < 0x1_0000

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  const UINT32_LIMIT := 0x1_0000_0000
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

  // Here is a generate function for converting any byte sequence to a nat.
  // The intention is that this function should be "obviously correct".
  // The SeqWithUInt32Suffix(s, n) lemma below can then be used to establish
  // SeqToNat(s) == n, provided appropriate conditions hold of s and n.
  function SeqToNat(s: seq<uint8>): nat {
    if s == [] then
      0
    else
      var last := |s| - 1;
      SeqToNat(s[..last]) * 0x100 + s[last] as nat
  }

  // This lemma says that prepending a 0 to a byte sequence does not change its
  // SeqToNat value. The lemma is used in the proof of SeqWithUInt32Suffix below.
  lemma SeqToNatZeroPrefix(s: seq<uint8>)
    ensures SeqToNat(s) == SeqToNat([0] + s)
  {
    if s == [] {
    } else {
      var s' := [0] + s;
      var last := |s| - 1;
      calc {
        SeqToNat(s');
      ==  // def. SeqToNat
        SeqToNat(s'[..|s|]) * 0x100 + s'[|s|] as nat;
      ==  { assert s'[..|s|] == [0] + s[..|s|-1] && s'[|s|] == s[last]; }
        SeqToNat([0] + s[..last]) * 0x100 + s[last] as nat;
      ==  { SeqToNatZeroPrefix(s[..last]); }
        SeqToNat(s[..last]) * 0x100 + s[last] as nat;
      ==  // def. SeqToNat
        SeqToNat(s);
      }
    }
  }

  // By the following lemma, the condition SeqToNat(s) == n
  // follows from the conditions in the preconditions.
  lemma SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
    requires n < UINT32_LIMIT
    requires 4 <= |s|
    requires var but4 := |s| - 4;
      s[but4..] == UInt32ToSeq(n as uint32) &&
      forall i :: 0 <= i < but4 ==> s[i] == 0
    ensures SeqToNat(s) == n
  {
    if |s| == 4 {
      calc {
        SeqToNat(s);
      ==
        SeqToNat(s[..3]) * 0x100 + s[3] as nat;
      ==  { assert s[..3][..2] == s[..2] && s[..3][2] == s[2]; }
        (SeqToNat(s[..2])
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      ==  { assert s[..2][..1] == s[..1] && s[..2][1] == s[1]; }
        ((SeqToNat(s[..1])
          * 0x100 + s[1] as nat)
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      ==  { assert s[..1][..0] == s[..0] && s[..1][0] == s[0]; }
        (((SeqToNat(s[..0])
          * 0x100 + s[0] as nat)
          * 0x100 + s[1] as nat)
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      }
    } else {
      assert s == [0] + s[1..];
      SeqToNatZeroPrefix(s[1..]);
      SeqWithUInt32Suffix(s[1..], n);
    }
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

  function method {:opaque} UInt64ToSeq(x: uint64): seq<uint8>
    ensures |UInt64ToSeq(x)| == 8
  {
    var bv := x as bv64;
    var b0 := ((bv >> 56)       ) as uint8;
    var b1 := ((bv >> 48) & 0xFF) as uint8;
    var b2 := ((bv >> 40) & 0xFF) as uint8;
    var b3 := ((bv >> 32) & 0xFF) as uint8;
    var b4 := ((bv >> 24) & 0xFF) as uint8;
    var b5 := ((bv >> 16) & 0xFF) as uint8;
    var b6 := ((bv >>  8) & 0xFF) as uint8;
    var b7 := ((bv      ) & 0xFF) as uint8;
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }

  function method {:opaque} SeqToUInt64(s: seq<uint8>): uint64
    requires |s| == 8
  {
    ( ((s[0] as bv64) << 56)
    | ((s[1] as bv64) << 48)
    | ((s[2] as bv64) << 40)
    | ((s[3] as bv64) << 32)
    | ((s[4] as bv64) << 24)
    | ((s[5] as bv64) << 16)
    | ((s[6] as bv64) <<  8)
    | ((s[7] as bv64)      )
    ) as uint64
  }
}
