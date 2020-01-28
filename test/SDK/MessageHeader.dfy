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

  method {:test} TestValidKVPair() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPair := (keyA, valA);
    r := Require(MessageHeader.ValidKVPair(kvPair));
  }

  method {:test} TestValidKVPairTooLong() returns (r: Result<()>) {
    var keyA := UTF8.Encode("keyA").value;
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var kvPair := (keyA, invalidVal);
    r := Require(!MessageHeader.ValidKVPair(kvPair));
  }

  method {:test} TestKVPairEntriesLength() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    var len := MessageHeader.KVPairEntriesLength(kvPairs, 0, |kvPairs|);

    r := RequireEqual(len, 2 + |keyA| + 2 + |valA|);
  }

  method {:test} TestKVPairsLength() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    var len := MessageHeader.KVPairsLength(kvPairs);

    r := RequireEqual(len, 2 + 2 + |keyA| + 2 + |valA|);
  }

  method {:test} TestValidAAD() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    r := Require(MessageHeader.ValidAAD(kvPairs));
  }

  method {:test} TestValidAADInvalidPairs() returns (r: Result<()>) {
    var keyA := UTF8.Encode("keyA").value;
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var kvPairs := [(keyA, invalidVal)];
    r := Require(!MessageHeader.ValidAAD(kvPairs));
  }

  // TODO test for true if EC is just under serialization size limit of 0x1_0000

  // TODO test for false if EC exceeds serialization size limit of 0x1_0000
  
  method {:test} TestValidKVPairs() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    r := Require(MessageHeader.ValidKVPairs(kvPairs));
  }

  method {:test} TestValidKVPairsInvalidPair() returns (r: Result<()>) {
    var keyA := UTF8.Encode("keyA").value;
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var kvPairs := [(keyA, invalidVal)];
    r := Require(!MessageHeader.ValidKVPairs(kvPairs));
  }

  method {:test} TestValidKVPairsUnsorted() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var keyB, valB := UTF8.Encode("keyB").value, UTF8.Encode("valB").value;
    var kvPairs := [(keyB, valB), (keyA, valA)];
    r := Require(!MessageHeader.ValidKVPairs(kvPairs));
  }

  method {:test} TestSortedKVPairs() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var keyB, valB := UTF8.Encode("keyB").value, UTF8.Encode("valB").value;
    var kvPairs := [(keyA, valA), (keyB, valB)];
    r := Require(MessageHeader.SortedKVPairs(kvPairs));
  }

  method {:test} TestSortedKVPairsHasDuplicate() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA), (keyA, valA)];
    r := Require(MessageHeader.SortedKVPairs(kvPairs));
  }

  method {:test} TestSortedKVPairsEmpty() returns (r: Result<()>) {
    r := Require(MessageHeader.SortedKVPairs([]));
  }

  method {:test} TestSortedKVPairsUnsorted() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var keyB, valB := UTF8.Encode("keyB").value, UTF8.Encode("valB").value;
    var kvPairs := [(keyB, valB), (keyA, valA)];
    r := Require(!MessageHeader.ValidKVPairs(kvPairs));
  }

  method {:test} TestKVPairsToSeq() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPairs := [(keyA, valA)];
    reveal MessageHeader.ValidKVPairs();
    var expectedBytes := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    r := RequireEqual(MessageHeader.KVPairsToSeq(kvPairs), expectedBytes);
  }

  // TODO: test KVPairsToSeq up to serialization size limit (2^16)

  method {:test} TestKVPairEntriesToSeq() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var keyB, valB := UTF8.Encode("keyB").value, UTF8.Encode("valB").value;
    var kvPairs := [(keyA, valA), (keyB, valB)];
    var expectedBytes := [0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];
    r := RequireEqual(MessageHeader.KVPairEntriesToSeq(kvPairs, 0, |kvPairs|), expectedBytes);
  }

  // TODO: test KVPairEntriesToSeq up to serialization size limit (2^16 - 2)

  method {:test} TestKVPairToSeq() returns (r: Result<()>) {
    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var kvPair := (keyA, valA);
    var expectedBytes := [0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    r := RequireEqual(MessageHeader.KVPairToSeq(kvPair), expectedBytes);
  }

  // TODO: test KVPairEntriesToSeq up to serialization size limit (2^16 - 4)
}
