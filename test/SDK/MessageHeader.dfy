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

  method {:test} TestKVPairSequenceToMapEmpty() returns (r: Result<()>) {
    var kvPairs := [];
    var output := MessageHeader.KVPairSequenceToMap(kvPairs);
    var expected := map[];
    r := RequireEqual(output, expected);
  }

  method {:test} TestKVPairSequenceToMap() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");
    var kvPairs := [(keyA, valA), (keyB, valB)];
    var output := MessageHeader.KVPairSequenceToMap(kvPairs);
    var expected := map[keyA := valA, keyB := valB];
    r := RequireEqual(output, expected);
  }

  method {:test} TestComputeValidAADEmpty() returns (r: Result<()>) {
    var encCtx := map[];
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADOnePair() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encCtx := map[keyA := valA];
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADOnePairMaxSize() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("A");
    // (2^16 - 1) - 2 => 65533 is the size that we want the key value pairs to fill
    // 65533 - 2 - 1 - 2 => 65528 is the size that we want the value to fill
    var largeVal := seq(65528, _ => 0);
    var encCtx := map[keyA := largeVal];
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(valid);
  }

  method {:test} TestComputeValidAADTooLarge() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("keyA");
    var keyB :- UTF8.Encode("keyB");
    var invalidVal := seq(65528, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var encCtx := map[keyA := invalidVal, keyB := invalidVal];

    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(!valid);
  }

  method {:test} TestComputeValidAADPairTooBig() returns (r: Result<()>) {
    var key :- UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    var encCtx := map[key := invalidVal];
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(!valid);
  }

  method {:test} TestComputeKVPairsLengthEmpty() returns (r: Result<()>) {
    var encCtx := map[];

    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    r := RequireEqual(len as int, 0);
  }

  method {:test} TestComputeKVPairsLengthOnePair() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encCtx := map[keyA := valA];

    var expectedSerialization := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    r := RequireEqual(len as int, |expectedSerialization|);
  }

  method {:test} TestComputeKVPairsLengthLong() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("A");
    var largeVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var encCtx := map[keyA := largeVal];
    
    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    r := RequireEqual(len as int, 7 + |largeVal|); // 7 bytes needed for kvPairs count, key size, and key
  }

  method {:test} TestComputeOpoerationsOnLargeValidEC() returns (r: Result<()>) {
    var encCtx :- TestUtils.GenerateLargeValidEncryptionContext();

    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    var _ :- RequireEqual(len as int, 2 + |encCtx| as int * 7);

    var valid := MessageHeader.ComputeValidAAD(encCtx);
    r := Require(valid);
  }
}
