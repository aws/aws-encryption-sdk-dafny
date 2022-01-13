// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/AwsCryptographicMaterialProviders/Materials.dfy"
include "../../src/SDK/Serialize/EncryptionContext.dfy"
include "../../src/SDK/Serialize/SerializableTypes.dfy"
include "../../src/Crypto/AESEncryption.dfy"

module {:extern "TestUtils"} TestUtils {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import MaterialProviders.Materials
  import EncryptionContext
  import AESEncryption
  import SerializableTypes

  const SHARED_TEST_KEY_ARN := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

  // TODO correctly verify UTF8 validity of long sequences
  // This axiom should only be used by tests to skip UTF8 verification of long sequences
  // long to be serialized in 16 bytes, in order to avoid a false negative for from verification.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1000
    ensures UTF8.ValidUTF8Seq(s)

  method GenerateInvalidEncryptionContext() returns (encCtx: EncryptionContext.Crypto.EncryptionContext)
  {
    var validUTF8char: UTF8.ValidUTF8Bytes :- expect UTF8.Encode("a");
    var key: UTF8.ValidUTF8Bytes := [];
    while |key| < UINT16_LIMIT {
      UTF8.ValidUTF8Concat(key, validUTF8char);
      key := key + validUTF8char;
    }
    encCtx := map[key := [0]];
  }

  // Generates a large encryption context that approaches the upper bounds of
  // what is able to be serialized in the message format.
  // Building a map item by item is slow in dafny, so this method should be used sparingly.
  method GenerateLargeValidEncryptionContext() returns (r: SerializableTypes.ESDKEncryptionContext)
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
    expect SerializableTypes.IsESDKEncryptionContext(encCtx);

    return encCtx;
  }

  method ExpectSerializableEncryptionContext(encCtx: EncryptionContext.Crypto.EncryptionContext)
    ensures SerializableTypes.IsESDKEncryptionContext(encCtx);
  {
    expect SerializableTypes.IsESDKEncryptionContext(encCtx);
  }

  method ExpectNonSerializableEncryptionContext(encCtx: EncryptionContext.Crypto.EncryptionContext) {
    expect !SerializableTypes.IsESDKEncryptionContext(encCtx);
  }

  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

  method SmallEncryptionContext(v: SmallEncryptionContextVariation)
    returns (encryptionContext: SerializableTypes.ESDKEncryptionContext)
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
    // ValidSmallEncryptionContext(encryptionContext);
  }

  // lemma ValidSmallEncryptionContext(encryptionContext: EncryptionContext.Crypto.EncryptionContext)
  //   requires |encryptionContext| <= 5
  //   requires forall k :: k in encryptionContext.Keys ==> |k| < 100 && |encryptionContext[k]| < 100
  // {
  //   assert SerializableTypes.Length(encryptionContext) < UINT16_LIMIT by {
  //     if |encryptionContext| != 0 {
  //       var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
  //       var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => SerializableTypes.Pair(keys[i], encryptionContext[keys[i]]));
  //       assert SerializableTypes.Length(encryptionContext) ==
  //         2 + SerializableTypes.LinearLength(kvPairs);

  //       var n := |kvPairs|;
  //       assert n <= 5;

  //       assert SerializableTypes.LinearLength(kvPairs) <= n * 204 by {
  //         KVPairsLengthBound(kvPairs, |kvPairs|, 200);
  //       }
  //       assert n * 204 <= 1020 < UINT16_LIMIT;
  //     }
  //   }
  // }

  // lemma KVPairsLengthBound(
  //   kvPairs: SerializableTypes.Linear<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>,
  //   n: nat,
  //   kvBound: int
  // )
  //   requires n <= |kvPairs|
  //   requires forall i :: 0 <= i < n ==> |kvPairs[i].key| + |kvPairs[i].value| <= kvBound
  //   ensures SerializableTypes.LinearLength(kvPairs) <= n * (4 + kvBound)
  // {
  // }

  // method MakeAESKeyring() returns (res: Result<RawAESKeyringDef.RawAESKeyring, string>)
  // {
  //   var namespace :- UTF8.Encode("namespace");
  //   var name :- UTF8.Encode("MyKeyring");
  //   var keyring := new RawAESKeyringDef.RawAESKeyring(
  //     namespace,
  //     name,
  //     seq(32, i => 0),
  //     AESEncryption.AES_GCM(
  //       keyLength := 32 as AESEncryption.KeyLength,
  //       tagLength := 16 as AESEncryption.TagLength,
  //       ivLength := 12 as AESEncryption.IVLength
  //     ));
  //   return Success(keyring);
  // }

  method NamespaceAndName(n: nat) returns (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes)
    requires 0 <= n < 10
    ensures |namespace| < UINT16_LIMIT
    ensures |name| < UINT16_LIMIT
  {
    var s := "child" + [n as char + '0'];
    namespace :- expect UTF8.Encode(s + " Namespace");
    name :- expect UTF8.Encode(s + " Name");
  }

  method {:extern} WriteFile(path: string, contents: seq<uint8>) returns (outcome: Outcome<string>)

  method {:extern} ReadFile(path: string) returns (result: Result<seq<uint8>, string>)
}
