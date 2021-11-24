// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/AwsCryptographicMaterialProviders/Materials.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../Util/TestUtils.dfy"

module TestMessageHeader {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import MaterialProviders.Materials
  import UTF8
  import EncryptionContext
  import opened TestUtils

  method {:test} TestKVPairSequenceToMapEmpty() {
    var kvPairs := [];
    var output := EncryptionContext.LinearToMap(kvPairs);
    var expected := map[];
    expect output == expected;
  }

  method {:test} TestKVPairSequenceToMap() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var kvPairs := [(keyA, valA), (keyB, valB)];
    var output := EncryptionContext.LinearToMap(kvPairs);
    var expected := map[keyA := valA, keyB := valB];
    expect output == expected;
  }

  method {:test} TestCheckSerializableEmpty() {
    var encCtx := map[];
    ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];
    ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableOnePairMaxSize() {
    var keyA :- expect UTF8.Encode("A");
    // (2^16 - 1) - 2 => 65533 is the size that we want the key value pairs to fill
    // 65533 - 2 - 1 - 2 => 65528 is the size that we want the value to fill
    var largeVal := seq(65528, _ => 0);
    var encCtx := map[keyA := largeVal];
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableTooLarge() {
    var keyA :- expect UTF8.Encode("keyA");
    var keyB :- expect UTF8.Encode("keyB");
    var invalidVal := seq(65528, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var encCtx := map[keyA := invalidVal, keyB := invalidVal];

    ExpectNonSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializablePairTooBig() {
    var key :- expect UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    var encCtx := map[key := invalidVal];
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    ExpectNonSerializableEncryptionContext(encCtx);
  }

  method {:test} TestComputeKVPairsLengthEmpty() {
    var encCtx := map[];

    var len := EncryptionContext.ComputeLength(encCtx);
    expect len as int == 0;
  }

  method {:test} TestComputeKVPairsLengthOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];

    var expectedSerialization := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    var len := EncryptionContext.ComputeLength(encCtx);
    expect len as int == |expectedSerialization|;
  }

  method {:test} TestComputeKVPairsLengthLong() {
    var keyA :- expect UTF8.Encode("A");
    var largeVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var encCtx := map[keyA := largeVal];

    var len := EncryptionContext.ComputeLength(encCtx);
    expect len as int == 7 + |largeVal|; // 7 bytes needed for kvPairs count, key size, and key
  }

  method {:test} TestComputeOpoerationsOnLargeValidEC() {
    var encCtx := TestUtils.GenerateLargeValidEncryptionContext();

    var len := EncryptionContext.ComputeLength(encCtx);
    expect len as int == 2 + |encCtx| as int * 7;

    ExpectSerializableEncryptionContext(encCtx);
  }
}
