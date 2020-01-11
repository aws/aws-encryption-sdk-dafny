module StandardLibrary.UInt {

  // TODO: Depend on types defined in dafny-lang/libraries instead
  newtype uint8 = x | 0 <= x < 0x100
  newtype uint16 = x | 0 <= x < 0x1_0000
  newtype uint32 = x | 0 <= x < 0x1_0000_0000
  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  const UINT16_LIMIT := 0x1_0000
  const UINT32_LIMIT := 0x1_0000_0000

  predicate method UInt8Less(a: uint8, b: uint8) { a < b }

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
  {
    var x0 := s[0] as uint16 * 0x100;
    x0 + s[1] as uint16
  }

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

  function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
    ensures |ret| == 8
    // TODO: Add postcondition. Both of these post conditions should be correct but require multiple lemmas to verify
    //ensures ((ret[0] as bv64) << 56) as uint64 + ((ret[1] as bv64) << 48) as uint64 + ((ret[2] as bv64) << 40) as uint64 +
    //  ((ret[3] as bv64) << 32) as uint64 + ((ret[4] as bv64) << 24) as uint64 + ((ret[5] as bv64) << 16) as uint64 +
    //  ((ret[6] as bv64) << 8) as uint64 + ret[7] as uint64 == x
    //ensures 0x100_0000_0000_0000 * ret[0] as uint64 + 0x1_0000_0000_0000 * ret[1] as uint64 +
    //  0x100_0000_0000 * ret[2] as uint64 + 0x1_0000_0000 * ret[3] as uint64 + 0x100_0000 * ret[4] as uint64 +
    //  0x1_0000 * ret[5] as uint64 + 0x100 * ret[6] as uint64 + ret[7] as uint64 == x
  {
    // Convert the uint64 to a bitvector. The bitvector can then be shifted right by some number of bits, and "& 0xFF"
    // can be performed to mask everything except the last 8 bits. This allows us to break up the 64 bit vector into
    // 8 uint8 portions.
    var bv := x as bv64;
    // Shift right and then take the final 8 bits. This means b0 represents the first (left-most) 8 bits of the uint64,
    // b1 represents the next 8 bits, etc.
    // b0 does not use "& 0xFF" since 64 bits shift 56 bits is the final 8 bits (so masking would just be redundant)
    var b0 := (bv >> 56) as uint8;
    var b1 := ((bv >> 48) & 0xFF) as uint8;
    var b2 := ((bv >> 40) & 0xFF) as uint8;
    var b3 := ((bv >> 32) & 0xFF) as uint8;
    var b4 := ((bv >> 24) & 0xFF) as uint8;
    var b5 := ((bv >> 16) & 0xFF) as uint8;
    var b6 := ((bv >>  8) & 0xFF) as uint8;
    // Do not shift at all, the masking handles the final 8 bits
    var b7 := (bv & 0xFF) as uint8;
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }

  // This function is used in the lemma proofs below
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
        SeqToNat(s[..3]) * 0x100 + s[3] as nat;
      ==  { assert s[..3][..2] == s[..2] && s[..3][2] == s[2]; }
        (SeqToNat(s[..2]) * 0x100 + s[2] as nat) * 0x100 + s[3] as nat;
      ==  { assert s[..2][..1] == s[..1] && s[..2][1] == s[1]; }
        ((SeqToNat(s[..1]) * 0x100 + s[1] as nat) * 0x100 + s[2] as nat) * 0x100 + s[3] as nat;
      ==  { assert s[..1][..0] == s[..0] && s[..1][0] == s[0]; }
        (((SeqToNat(s[..0]) * 0x100 + s[0] as nat) * 0x100 + s[1] as nat) * 0x100 + s[2] as nat) * 0x100 + s[3] as nat;
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
