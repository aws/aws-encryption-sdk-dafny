// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

module StandardLibrary.UInt {

  // TODO: Depend on types defined in dafny-lang/libraries instead
  newtype uint8 = x | 0 <= x < 0x100
  newtype uint16 = x | 0 <= x < 0x1_0000
  newtype uint32 = x | 0 <= x < 0x1_0000_0000
  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
  newtype posInt64 = x | 0 < x < 0x8000_0000_0000_0000 witness 1

  const UINT16_LIMIT := 0x1_0000
  const UINT32_LIMIT := 0x1_0000_0000
  const UINT64_LIMIT := 0x1_0000_0000_0000_0000
  const INT32_MAX_LIMIT := 0x8000_0000
  const INT64_MAX_LIMIT := 0x8000_0000_0000_0000

  predicate method UInt8Less(a: uint8, b: uint8) { a < b }

  predicate method HasUint16Len<T>(s: seq<T>) {
    |s| < UINT16_LIMIT
  }

  type seq16<T> = s: seq<T> | HasUint16Len(s)
  type Uint8Seq16 = seq16<uint8>

  predicate method HasUint32Len<T>(s: seq<T>) {
    |s| < UINT32_LIMIT
  }

  type seq32<T> = s: seq<T> | HasUint32Len(s)
  type Uint8Seq32 = seq32<uint8>

  predicate method HasUint64Len<T>(s: seq<T>) {
    |s| < UINT64_LIMIT
  }

  type seq64<T> = s: seq<T> | HasUint64Len(s)
  type Uint8Seq64 = seq64<uint8>

  function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
    ensures |ret| == 2
    ensures 0x100 * ret[0] as uint16 + ret[1] as uint16 == x
  {
    var b0 := (x / 0x100) as uint8;
    var b1 := (x % 0x100) as uint8;
    [b0, b1]
  }

  function method SeqToUInt16(s: seq<uint8>): (x: uint16)
    requires |s| == 2
    ensures UInt16ToSeq(x) == s
    ensures x >= 0
  {
    var x0 := s[0] as uint16 * 0x100;
    x0 + s[1] as uint16
  }

  lemma UInt16SeqSerializeDeserialize(x: uint16)
    ensures SeqToUInt16(UInt16ToSeq(x)) == x
  {}

  lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 2
    ensures UInt16ToSeq(SeqToUInt16(s)) == s
  {}

  function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
    ensures |ret| == 4
    ensures 0x100_0000 * ret[0] as uint32 + 0x1_0000 * ret[1] as uint32 + 0x100 * ret[2] as uint32 + ret[3] as uint32 == x
  {
    var b0 := (x / 0x100_0000) as uint8;
    var x0 := x - (b0 as uint32 * 0x100_0000);

    var b1 := (x0 / 0x1_0000) as uint8;
    var x1 := x0 - (b1 as uint32 * 0x1_0000);

    var b2 := (x1 / 0x100) as uint8;
    var b3 := (x1 % 0x100) as uint8;
    [b0, b1, b2, b3]
  }

  function method SeqToUInt32(s: seq<uint8>): (x: uint32)
    requires |s| == 4
    ensures UInt32ToSeq(x) == s
  {
    var x0 := s[0] as uint32 * 0x100_0000;
    var x1 := x0 + s[1] as uint32 * 0x1_0000;
    var x2 := x1 + s[2] as uint32 * 0x100;
    x2 + s[3] as uint32
  }

  lemma UInt32SeqSerializeDeserialize(x: uint32)
    ensures SeqToUInt32(UInt32ToSeq(x)) == x
  {}

  lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 4
    ensures UInt32ToSeq(SeqToUInt32(s)) == s
  {}

  function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
    ensures |ret| == 8
    ensures 0x100_0000_0000_0000 * ret[0] as uint64 + 0x1_0000_0000_0000 * ret[1] as uint64 +
      0x100_0000_0000 * ret[2] as uint64 + 0x1_0000_0000 * ret[3] as uint64 + 0x100_0000 * ret[4] as uint64 +
      0x1_0000 * ret[5] as uint64 + 0x100 * ret[6] as uint64 + ret[7] as uint64 == x
  {
    var b0 := (x / 0x100_0000_0000_0000) as uint8;
    var x0 := x - (b0 as uint64 * 0x100_0000_0000_0000);

    var b1 := (x0 / 0x1_0000_0000_0000) as uint8;
    var x1 := x0 - (b1 as uint64 * 0x1_0000_0000_0000);

    var b2 := (x1 / 0x100_0000_0000) as uint8;
    var x2 := x1 - (b2 as uint64 * 0x100_0000_0000);

    var b3 := (x2 / 0x1_0000_0000) as uint8;
    var x3 := x2 - (b3 as uint64 * 0x1_0000_0000);

    var b4 := (x3 / 0x100_0000) as uint8;
    var x4 := x3 - (b4 as uint64 * 0x100_0000);

    var b5 := (x4 / 0x1_0000) as uint8;
    var x5 := x4 - (b5 as uint64 * 0x1_0000);

    var b6 := (x5 / 0x100) as uint8;
    var b7 := (x5 % 0x100) as uint8;
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }

  function method SeqToUInt64(s: seq<uint8>): (x: uint64)
    requires |s| == 8
    ensures UInt64ToSeq(x) == s
  {
    var x0 := s[0] as uint64 * 0x100_0000_0000_0000;
    var x1 := x0 + s[1] as uint64 * 0x1_0000_0000_0000;
    var x2 := x1 + s[2] as uint64 * 0x100_0000_0000;
    var x3 := x2 + s[3] as uint64 * 0x1_0000_0000;
    var x4 := x3 + s[4] as uint64 * 0x100_0000;
    var x5 := x4 + s[5] as uint64 * 0x1_0000;
    var x6 := x5 + s[6] as uint64 * 0x100;
    var x := x6 + s[7] as uint64;
    UInt64SeqSerialize(x, s);
    x
  }

  lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
    requires |s| == 8
    requires 0x100_0000_0000_0000 * s[0] as uint64
      + 0x1_0000_0000_0000 * s[1] as uint64
      + 0x100_0000_0000 * s[2] as uint64
      + 0x1_0000_0000 * s[3] as uint64
      + 0x100_0000 * s[4] as uint64
      + 0x1_0000 * s[5] as uint64
      + 0x100 * s[6] as uint64
      + s[7] as uint64 == x
    ensures UInt64ToSeq(x) == s
  {
    calc {
      UInt64ToSeq(x);
    ==
      UInt64ToSeq(s[0] as uint64 * 0x100_0000_0000_0000
      + s[1] as uint64 * 0x1_0000_0000_0000
      + s[2] as uint64 * 0x100_0000_0000
      + s[3] as uint64 * 0x1_0000_0000
      + s[4] as uint64 * 0x100_0000
      + s[5] as uint64 * 0x1_0000
      + s[6] as uint64 * 0x100
      + s[7] as uint64);
    ==
      var b0 := ((s[0] as uint64 * 0x100_0000_0000_0000
        + s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64) / 0x100_0000_0000_0000) as uint8;
      assert b0 == s[0];
      var x0 := (s[0] as uint64 * 0x100_0000_0000_0000
        + s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64) - (b0 as uint64 * 0x100_0000_0000_0000);
      assert x0 == (s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b1 := (x0 / 0x1_0000_0000_0000) as uint8;
      assert b1 == s[1];
      var x1 := x0 - (b1 as uint64 * 0x1_0000_0000_0000);
      assert x1 == (s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b2 := (x1 / 0x100_0000_0000) as uint8;
      assert b2 == s[2];
      var x2 := x1 - (b2 as uint64 * 0x100_0000_0000);
      assert x2 == (s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b3 := (x2 / 0x1_0000_0000) as uint8;
      assert b3 == s[3];
      var x3 := x2 - (b3 as uint64 * 0x1_0000_0000);
      assert x3 == (s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b4 := (x3 / 0x100_0000) as uint8;
      assert b4 == s[4];
      var x4 := x3 - (b4 as uint64 * 0x100_0000);
      assert x4 == (s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b5 := (x4 / 0x1_0000) as uint8;
      assert b5 == s[5];
      var x5 := x4 - (b5 as uint64 * 0x1_0000);
      assert x5 == (s[6] as uint64 * 0x100 + s[7] as uint64);

      var b6 := (x5 / 0x100) as uint8;
      assert b6 == s[6];
      var b7 := (x5 % 0x100) as uint8;
      assert b7 == s[7];
      [b0, b1, b2, b3, b4, b5, b6, b7];
    ==
      [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]];
    ==
      s;
    }
  }

  lemma UInt64SeqSerializeDeserialize(x: uint64)
    ensures SeqToUInt64(UInt64ToSeq(x)) == x
  {}

  lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 8
    ensures UInt64ToSeq(SeqToUInt64(s)) == s
  {}

  function SeqToNat(s: seq<uint8>): nat {
    if s == [] then
      0
    else
      var finalIndex := |s| - 1;
      SeqToNat(s[..finalIndex]) * 0x100 + s[finalIndex] as nat
  }

  // By the following lemma, prepending a 0 to a byte sequence does not change its SeqToNat value
  lemma SeqToNatZeroPrefix(s: seq<uint8>)
    ensures SeqToNat(s) == SeqToNat([0] + s)
  {
    if s == [] {
    } else {
      var s' := [0] + s;
      var sLength := |s|;
      var sFinalIndex := sLength - 1;
      calc {
        SeqToNat(s);
      ==
        SeqToNat(s[..sFinalIndex]) * 0x100 + s[sFinalIndex] as nat;
      ==
        SeqToNat([0] + s[..sFinalIndex]) * 0x100 + s[sFinalIndex] as nat;
      == { assert (s'[..sLength] == [0] + s[..sFinalIndex]) && s'[sLength] == s[sFinalIndex]; }
        SeqToNat(s'[..sLength]) * 0x100 + s'[sLength] as nat;
      ==
        SeqToNat(s');
      ==
        SeqToNat([0] + s);
      }
    }
  }

  // By the following lemma, SeqToNat(s) == n is automatically true if the given preconditions are true
  lemma SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
    requires n < UINT32_LIMIT
    requires 4 <= |s|
    requires var suffixStartIndex := |s| - 4;
      (s[suffixStartIndex..] == UInt32ToSeq(n as uint32)) &&
      (forall i :: 0 <= i < suffixStartIndex ==> s[i] == 0)
    ensures SeqToNat(s) == n
  {
    if |s| == 4 {
      calc {
        SeqToNat(s);
      ==
        SeqToNat(s[..3])
          * 0x100 + s[3] as nat;
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
      ==
        n;
      }
    } else {
      assert s == [0] + s[1..];
      SeqToNatZeroPrefix(s[1..]);
      SeqWithUInt32Suffix(s[1..], n);
    }
  }
}
