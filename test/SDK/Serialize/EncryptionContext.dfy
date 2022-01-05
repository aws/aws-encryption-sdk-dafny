// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/SDK/Serialize/EncryptionContext.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../Util/TestUtils.dfy"
include "../../../src/SDK/Serialize/SerializableTypes.dfy"

module TestSerialize {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import EncryptionContext
  import TestUtils
  import SerializableTypes

  method {:test} TestSerializeAAD() {
    // var wr := new Streams.ByteWriter();
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    expect SerializableTypes.IsESDKEncryptionContext(encryptionContext);

    var expectedSerializedAAD := [0, 26, 0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];

    var test := EncryptionContext.WriteAADSection(EncryptionContext.GetCanonicalEncryptionContext(encryptionContext));
    expect test == expectedSerializedAAD;
  }

  method {:test} TestSerializeAADEmpty() {
    var encryptionContext := map[];

    var expectedSerializedAAD := [0, 0];

    var test := EncryptionContext.WriteAADSection(EncryptionContext.GetCanonicalEncryptionContext(encryptionContext));
    expect test == expectedSerializedAAD;
  }

  method {:test} TestSerializeLargeValidEC() {
    var encryptionContext := TestUtils.GenerateLargeValidEncryptionContext();

    var test := EncryptionContext.WriteAADSection(EncryptionContext.GetCanonicalEncryptionContext(encryptionContext));
    expect |test| == 4 + |encryptionContext| as int * 7;
  }

  method {:test} TestSerializeKVPairs() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var encryptionContext := map[keyB := valB, keyA := valA];
    expect SerializableTypes.IsESDKEncryptionContext(encryptionContext);

    var expectedSerializedAAD := [0, 2, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65, 0, 4, 107, 101, 121, 66, 0, 4, 118, 97, 108, 66];

    var test := EncryptionContext.WriteAAD(EncryptionContext.GetCanonicalEncryptionContext(encryptionContext));
    expect test == expectedSerializedAAD;
  }

  method {:test} TestKVPairSequenceToMapEmpty() {
    var kvPairs := [];
    var output := EncryptionContext.GetEncryptionContext(kvPairs);
    var expected := map[];
    expect output == expected;
  }

  method {:test} TestKVPairSequenceToMap() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    var kvPairs := [SerializableTypes.Pair(keyA, valA), SerializableTypes.Pair(keyB, valB)];

    // ESDKCanonicalEncryptionContext?(kvPairs) == true
    assert HasUint16Len(kvPairs);
    assert SerializableTypes.LinearLength(kvPairs) < 100;
    expect keyA != keyB;
    assert EncryptionContext.KeysAreUnique(kvPairs);

    var output := EncryptionContext.GetEncryptionContext(kvPairs);
    var expected := map[keyA := valA, keyB := valB];
    expect output == expected;
  }

  method {:test} TestCheckSerializableEmpty() {
    var encCtx := map[];
    TestUtils.ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];
    TestUtils.ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableOnePairMaxSize() {
    var keyA :- expect UTF8.Encode("A");
    // (2^16 - 1) - 2 => 65533 is the size that we want the key value pairs to fill
    // 65533 - 2 - 1 - 2 => 65528 is the size that we want the value to fill
    var largeVal := seq(65528, _ => 0);
    var encCtx := map[keyA := largeVal];
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    TestUtils.ExpectSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializableTooLarge() {
    var keyA :- expect UTF8.Encode("keyA");
    var keyB :- expect UTF8.Encode("keyB");
    var invalidVal := seq(65528, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    var encCtx := map[keyA := invalidVal, keyB := invalidVal];

    TestUtils.ExpectNonSerializableEncryptionContext(encCtx);
  }

  method {:test} TestCheckSerializablePairTooBig() {
    var key :- expect UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    var encCtx := map[key := invalidVal];
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    TestUtils.ExpectNonSerializableEncryptionContext(encCtx);
  }

  method {:test} TestComputeKVPairsLengthEmpty() {
    var encCtx := map[];

    var len := SerializableTypes.Length(encCtx);
    expect len as int == 0;
  }

  method {:test} TestComputeKVPairsLengthOnePair() {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encCtx := map[keyA := valA];

    var expectedSerialization := [0, 1, 0, 4, 107, 101, 121, 65, 0, 4, 118, 97, 108, 65];
    var len := SerializableTypes.Length(encCtx);
    expect len as int == |expectedSerialization|;
  }

  method {:test} TestComputeKVPairsLengthLong() {
    var keyA :- expect UTF8.Encode("A");
    var largeVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(largeVal);
    var encCtx := map[keyA := largeVal];

    var len := SerializableTypes.Length(encCtx);
    expect len as int == 7 + |largeVal|; // 7 bytes needed for kvPairs count, key size, and key
  }

  method {:test} TestComputeOpoerationsOnLargeValidEC() {
    var encCtx := TestUtils.GenerateLargeValidEncryptionContext();

    var len := SerializableTypes.Length(encCtx);
    expect len as int == 2 + |encCtx| as int * 7;

    TestUtils.ExpectSerializableEncryptionContext(encCtx);
  }

}
