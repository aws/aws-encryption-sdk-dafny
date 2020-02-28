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

  method {:test} TestKVPairSequenceToMapEmpty() {
    var kvPairs := [];
    var output := MessageHeader.KVPairSequenceToMap(kvPairs);
    var expected := map[];
    expect output == expected;
  }

  method {:test} TestKVPairSequenceToMap() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var kvPairs := [(keyA, valA), (keyB, valB)];
    var output := MessageHeader.KVPairSequenceToMap(kvPairs);
    var expected := map[keyA := valA, keyB := valB];
    expect output == expected;
  }

  method ExpectValidAAD(encCtx: Materials.EncryptionContext) {
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    expect valid;
  }

  method ExpectInvalidAAD(encCtx: Materials.EncryptionContext) {
    var valid := MessageHeader.ComputeValidAAD(encCtx);
    expect !valid;
  }

  method {:test} TestComputeValidAADEmpty() {
    var encCtx := map[];
    ExpectValidAAD(encCtx);
  }

  method {:test} TestComputeValidAADOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];
    ExpectValidAAD(encCtx);
  }

  method {:test} TestComputeValidAADOnePairMaxSize() {
    var keyA :- expect UTF8.Encode("A");
    // (2^16 - 1) - 2 => 65533 is the size that we want the key value pairs to fill
    // 65533 - 2 - 1 - 2 => 65528 is the size that we want the value to fill
    var largeVal := seq(65528, _ => 0);
    var encCtx := map[keyA := largeVal];
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    ExpectValidAAD(encCtx);
  }

  method {:test} TestComputeValidAADTooLarge() {
    var keyA :- expect UTF8.Encode("keyA");
    var keyB :- expect UTF8.Encode("keyB");
    var invalidVal := seq(65528, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var encCtx := map[keyA := invalidVal, keyB := invalidVal];

    ExpectInvalidAAD(encCtx);
  }

  method {:test} TestComputeValidAADPairTooBig() {
    var key :- expect UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    var encCtx := map[key := invalidVal];
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    ExpectInvalidAAD(encCtx);
  }

  method {:test} TestComputeKVPairsLengthEmpty() {
    var encCtx := map[];

    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    expect len as int == 0;
  }

  method {:test} TestComputeKVPairsLengthOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];

    var expectedSerialization := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    expect len as int == |expectedSerialization|;
  }

  method {:test} TestComputeKVPairsLengthLong() {
    var keyA :- expect UTF8.Encode("A");
    var largeVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var encCtx := map[keyA := largeVal];
    
    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    expect len as int == 7 + |largeVal|; // 7 bytes needed for kvPairs count, key size, and key
  }

  method {:test} TestComputeOpoerationsOnLargeValidEC() {
    var encCtx := TestUtils.GenerateLargeValidEncryptionContext();

    var len := MessageHeader.ComputeKVPairsLength(encCtx);
    expect len as int == 2 + |encCtx| as int * 7;

    var valid := MessageHeader.ComputeValidAAD(encCtx);
    expect valid;
  }
}
