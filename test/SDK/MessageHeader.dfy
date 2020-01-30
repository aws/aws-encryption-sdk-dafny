include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../Util/TestUtils.dfy"

module TestMessageHeader {
  import AlgorithmSuite
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import UTF8
  import MessageHeader
  import TestUtils
  
  method {:test} TestComputeValidAADEmpty() returns (r: Result<()>) {
    var kvPairs := [];
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADOnePair() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADOnePairMaxSize() returns (r: Result<()>) {
    var keyA := UTF8.Encode("A").value;
    // (2^16 - 1) - 2 => 65533 what we want the size of the key value pair to fill
    // 65533 - 2 - 1 - 2 => 65528 is the size that we want the value to fill
    var largeVal := seq(65528, _ => 0);
    var kvPairs :=[(keyA, largeVal)];
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADMaxPairs() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("A").value, UTF8.Encode("A").value;
    // (2^16 - 1) / (minimum kvPair size) => (2^16 - 1) / 6 => 10922 is the max
    // number of pairs you can stuff into a valid AAD
    var kvPairs := seq(10922, _ => (keyA, valA));
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADTooManyEntries() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := seq(0x1_0000, _ => (keyA, valA));
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(!valid);
  }

  method {:test} TestComputeValidAADTooLarge() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := seq(0x1_FFFF, _ => (keyA, valA));
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(!valid);
  }

  method {:test} TestComputeValidAADPairTooBig() returns (r: Result<()>) {
    var keyA := UTF8.Encode("keyA").value;
    var invalidVal := seq(0x1_0000, _ => 0);
    var kvPairs :=[(keyA, invalidVal)];
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(!valid);
  }

  method {:test} TestComputeValidAADUnsorted() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var keyB, valB := UTF8.Encode("keyB").value, UTF8.Encode("valB").value;
    var kvPairs := [(keyB, valB), (keyA, valA)];
    var valid := MessageHeader.ComputeValidAAD(kvPairs);
    r := Require(!valid);
  }

  method {:test} TestComputeKVPairsLengthEmpty() returns (r: Result<()>) {
    var kvPairs := [];

    var len := MessageHeader.ComputeKVPairsLength(kvPairs);
    r := RequireEqual(len as int, 0);
  }

  method {:test} TestComputeKVPairsLengthOnePair() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];

    var expectedSerialization := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    var len := MessageHeader.ComputeKVPairsLength(kvPairs);
    r := RequireEqual(len as int, |expectedSerialization|);
  }

  method {:test} TestComputeKVPairsLengthLong() returns (r: Result<()>) {
    var keyA := UTF8.Encode("A").value;
    var largeVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var kvPairs :=[(keyA, largeVal)];
    
    var len := MessageHeader.ComputeKVPairsLength(kvPairs);
    r := RequireEqual(len as int, 7 + |largeVal|); // 7 bytes needed for kvPairs count, key size, and key
  }
}
