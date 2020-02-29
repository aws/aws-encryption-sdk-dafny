include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/SDK/MessageHeader.dfy"

module {:extern "TestUtils"} TestUtils {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Materials
  import MessageHeader

  const SHARED_TEST_KEY_ARN := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

  // TODO correctly verify UTF8 validity of long sequences
  // This axiom should only be used by tests to skip UTF8 verification of long sequences
  // long to be serialized in 16 bytes, in order to avoid a false negative for from verification.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1000
    ensures UTF8.ValidUTF8Seq(s)
  
  // Generates a large encryption context that approaches the upper bounds of
  // what is able to be serialized in the message format.
  // Building a map item by item is slow in dafny, so this method should be used sparingly.
  method GenerateLargeValidEncryptionContext() returns (r: Materials.EncryptionContext)
    ensures MessageHeader.ValidAAD(r)
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

    assert MessageHeader.ValidAAD(encCtx) by {
      reveal MessageHeader.ValidAAD();
      assert MessageHeader.KVPairsLength(encCtx) < UINT16_LIMIT by {
        var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encCtx.Keys, UInt.UInt8Less);
        var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encCtx[keys[i]]));
        KVPairsLengthBound(kvPairs, |kvPairs|, 3);
        assert MessageHeader.KVPairEntriesLength(kvPairs, 0, |kvPairs|) <= 2 + numMaxPairs * 7;
      }
    }
    return encCtx;
  }

  lemma ValidSmallEncryptionContext(encryptionContext: Materials.EncryptionContext)
    requires |encryptionContext| <= 5
    requires forall k :: k in encryptionContext.Keys ==> |k| < 100 && |encryptionContext[k]| < 100
    ensures MessageHeader.ValidAAD(encryptionContext)
  {
    reveal MessageHeader.ValidAAD();
    assert MessageHeader.KVPairsLength(encryptionContext) < UINT16_LIMIT by {
      var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
      var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
      KVPairsLengthBound(kvPairs, |kvPairs|, 200);
      assert MessageHeader.KVPairEntriesLength(kvPairs, 0, |kvPairs|) <= 5 * 204;
    }
  }

  lemma KVPairsLengthBound(kvPairs: MessageHeader.EncryptionContextSeq, n: nat, kvBound: int)
    requires n <= |kvPairs|
    requires forall i :: 0 <= i < n ==> |kvPairs[i].0| + |kvPairs[i].1| <= kvBound
    ensures MessageHeader.KVPairEntriesLength(kvPairs, 0, n) <= n * (4 + kvBound)
  {
  }
}
