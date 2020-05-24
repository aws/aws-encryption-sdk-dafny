// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../../src/Crypto/RSAEncryption.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/SDK/MessageHeader.dfy"

module {:extern "TestUtils"} TestUtils {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Materials
  import EncryptionContext
  import MessageHeader
  import RSA = RSAEncryption
  import RawRSAKeyringDef

  const SHARED_TEST_KEY_ARN := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

  // TODO correctly verify UTF8 validity of long sequences
  // This axiom should only be used by tests to skip UTF8 verification of long sequences
  // long to be serialized in 16 bytes, in order to avoid a false negative for from verification.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1000
    ensures UTF8.ValidUTF8Seq(s)

  method GenerateInvalidEncryptionContext() returns (encCtx: EncryptionContext.Map)
    ensures !EncryptionContext.Serializable(encCtx)
  {
    var validUTF8char: UTF8.ValidUTF8Bytes :- expect UTF8.Encode("a");
    var key: UTF8.ValidUTF8Bytes := [];
    while |key| < UINT16_LIMIT {
      key := key + validUTF8char;
    }
    encCtx := map[key := [0]];
    //assert !MessageHeader.ValidKVPair((key, encCtx[key]));
    //assert !MessageHeader.ValidKVPairs(encCtx);
    //reveal MessageHeader.ValidAAD();
    reveal EncryptionContext.Serializable();
    assert !EncryptionContext.Serializable(encCtx);
  }

  // Generates a large encryption context that approaches the upper bounds of
  // what is able to be serialized in the message format.
  // Building a map item by item is slow in dafny, so this method should be used sparingly.
  method GenerateLargeValidEncryptionContext() returns (r: EncryptionContext.Map)
    ensures EncryptionContext.Serializable(r)
  {
    // KVPairsMaxSize - KVPairsLenLen / KVPairLen ==>
    // (2^16 - 1 - 2) / (2 + 2 + 2 + 1) ==> (2^16 - 3) / 7 ==> 9361
    // which is close to the max number of pairs you can stuff into a valid AAD.
    // We look for 9361 valid 2 byte UTF8 sequences (sticking to 2 bytes for simplicity).
    assert (0x1_0000 - 1 - 2) / (2 + 2 + 2 + 1) == (0x1_0000 - 3) / 7 == 9361;
    var numMaxPairs := 9361;
    var val :- expect UTF8.Encode("a");
    var encCtx: map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes> := map[];

    // Instead of proving termination for looking for Valid UTF8 sequences,
    // provide an upper bound to while loop
    var i := 0;
    while |encCtx| < numMaxPairs && i < 0x1_0000
      invariant forall k :: k in encCtx ==> |k| + |encCtx[k]| == 3
      decreases 0x1_0000 - i
    {
      var key := UInt16ToSeq(i as uint16);
      if UTF8.ValidUTF8Seq(key) {
        encCtx := encCtx[key := val];
      }
      i := i + 1;
    }
    // Check that we actually built a encCtx of the correct size
    expect |encCtx| == numMaxPairs;

    assert EncryptionContext.Serializable(encCtx) by {
      reveal EncryptionContext.Serializable();
      assert EncryptionContext.Length(encCtx) < UINT16_LIMIT by {
        var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encCtx.Keys, UInt.UInt8Less);
        var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encCtx[keys[i]]));
        KVPairsLengthBound(kvPairs, |kvPairs|, 3);
        assert EncryptionContext.LinearLength(kvPairs, 0, |kvPairs|) <= 2 + numMaxPairs * 7;
      }
    }
    return encCtx;
  }

  method ExpectSerializableEncryptionContext(encCtx: EncryptionContext.Map)
    ensures EncryptionContext.Serializable(encCtx)
  {
    var valid := EncryptionContext.CheckSerializable(encCtx);
    expect valid;
  }

  method ExpectNonSerializableEncryptionContext(encCtx: EncryptionContext.Map) {
    var valid := EncryptionContext.CheckSerializable(encCtx);
    expect !valid;
  }

  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

  method SmallEncryptionContext(v: SmallEncryptionContextVariation) returns (encryptionContext: EncryptionContext.Map)
    ensures EncryptionContext.Serializable(encryptionContext)
    ensures encryptionContext.Keys !! Materials.RESERVED_KEY_VALUES
  {
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var keyB :- expect UTF8.Encode("keyB");
    var valB :- expect UTF8.Encode("valB");
    match v {
      case Empty =>
        encryptionContext := map[];
      case A =>
        encryptionContext := map[keyA := valA];
      case AB =>
        encryptionContext := map[keyA := valA, keyB := valB];
      case BA =>
        // this is really the same as AB; this lets us test that this is also true at run time
        encryptionContext := map[keyB := valB, keyA := valA];
    }
    ValidSmallEncryptionContext(encryptionContext);
  }

  lemma ValidSmallEncryptionContext(encryptionContext: EncryptionContext.Map)
    requires |encryptionContext| <= 5
    requires forall k :: k in encryptionContext.Keys ==> |k| < 100 && |encryptionContext[k]| < 100
    ensures EncryptionContext.Serializable(encryptionContext)
  {
    reveal EncryptionContext.Serializable();
    assert EncryptionContext.Length(encryptionContext) < UINT16_LIMIT by {
      if |encryptionContext| != 0 {
        var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
        var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
        assert EncryptionContext.Length(encryptionContext) ==
          2 + EncryptionContext.LinearLength(kvPairs, 0, |kvPairs|);

        var n := |kvPairs|;
        assert n <= 5;

        assert EncryptionContext.LinearLength(kvPairs, 0, n) <= n * 204 by {
          KVPairsLengthBound(kvPairs, |kvPairs|, 200);
        }
        assert n * 204 <= 1020 < UINT16_LIMIT;
      }
    }
  }

  lemma KVPairsLengthBound(kvPairs: EncryptionContext.Linear, n: nat, kvBound: int)
    requires n <= |kvPairs|
    requires forall i :: 0 <= i < n ==> |kvPairs[i].0| + |kvPairs[i].1| <= kvBound
    ensures EncryptionContext.LinearLength(kvPairs, 0, n) <= n * (4 + kvBound)
  {
  }

  method MakeRSAKeyring() returns (res: Result<RawRSAKeyringDef.RawRSAKeyring>)
    ensures res.Success? ==> res.value.Valid()
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Repr)
  {
    var namespace :- UTF8.Encode("namespace");
    var name :- UTF8.Encode("MyKeyring");
    var ek, dk := RSA.GenerateKeyPair(2048, RSA.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace, name, RSA.PaddingMode.PKCS1, Some(ek), Some(dk));
    return Success(keyring);
  }

  method NamespaceAndName(n: nat) returns (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes)
    requires 0 <= n < 10
    ensures |namespace| < UINT16_LIMIT
    ensures |name| < UINT16_LIMIT
  {
    var s := "child" + [n as char + '0'];
    namespace :- expect UTF8.Encode(s + " Namespace");
    name :- expect UTF8.Encode(s + " Name");
  }
}
