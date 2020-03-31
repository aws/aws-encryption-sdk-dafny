include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"
include "../Util/Sets.dfy"

module {:extern "EncryptionContext"} EncryptionContext {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Sets

  /*
   * The main type of encryption context
   */

  type T = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

  predicate {:opaque} ValidAAD(encryptionContext: T) {
    && KVPairsLength(encryptionContext) < UINT16_LIMIT
    && ValidKVPairs(encryptionContext)
  }

  /*
   * Validity of key-value pairs in the encryption context
   */

  predicate method ValidKVPairs(encryptionContext: T) {
    && |encryptionContext| < UINT16_LIMIT
    && (forall key :: key in encryptionContext.Keys ==> ValidKVPair((key, encryptionContext[key])))
  }

  predicate method ValidKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)) {
    && |kvPair.0| < UINT16_LIMIT
    && |kvPair.1| < UINT16_LIMIT
    && UTF8.ValidUTF8Seq(kvPair.0)
    && UTF8.ValidUTF8Seq(kvPair.1)
  }

  /*
   * Length properties
   */

  function KVPairsLength(encryptionContext: T): nat
  {
    if |encryptionContext| == 0 then 0 else
      // Defining and reasoning about order at this level is simplified by using a sequence of
      // key value pairs instead of a map.
      var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
      var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
      2 + KVPairEntriesLength(kvPairs, 0, |kvPairs|)
  }

  /*
   * Encryption context as a sequence
   */

  // To make verification and working with iterating through the encryption context
  // simpler, here we define a specific type to represent a sequence of key-value tuples.
  type Linear = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  // Length of KVPairEntries is defined in terms of a seq of tuples, which is easier to reason about
  function KVPairEntriesLength(kvPairs: Linear, lo: nat, hi: nat): nat
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then 0 else
      KVPairEntriesLength(kvPairs, lo, hi - 1) +
      2 + |kvPairs[hi - 1].0| +
      2 + |kvPairs[hi - 1].1|
  }

  // There isn't an efficient way to build a map from a sequence in dafny, so this
  // extern is used specifically to convert a sequence of key value pairs to a map
  method {:extern "KVPairSequenceToMap"} KVPairSequenceToMap(kvPairs: Linear) returns (res: T)  // TODO: FromLinear

  /*
   * Useful lemmas about key-value pairs
   */

  lemma KVPairEntriesLengthSplit(kvPairs: Linear, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |kvPairs|
    ensures KVPairEntriesLength(kvPairs, lo, hi)
         == KVPairEntriesLength(kvPairs, lo, mid) + KVPairEntriesLength(kvPairs, mid, hi)
  {
  }

  lemma KVPairEntriesLengthPrefix(kvPairs: Linear, more: Linear)
    ensures KVPairEntriesLength(kvPairs + more, 0, |kvPairs|) == KVPairEntriesLength(kvPairs, 0, |kvPairs|)
  {
    var n := |kvPairs|;
    if n == 0 {
    } else {
      var last := kvPairs[n - 1];
      calc {
        KVPairEntriesLength(kvPairs + more, 0, n);
      ==  // def. KVPairEntriesLength
        KVPairEntriesLength(kvPairs + more, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs + more == kvPairs[..n - 1] + ([last] + more); }
        KVPairEntriesLength(kvPairs[..n - 1] + ([last] + more), 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { KVPairEntriesLengthPrefix(kvPairs[..n - 1], [last] + more); }
        KVPairEntriesLength(kvPairs[..n - 1], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { KVPairEntriesLengthPrefix(kvPairs[..n - 1], [last] + more); }
        KVPairEntriesLength(kvPairs[..n - 1] + [last], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs[..n - 1] + [last] == kvPairs; }
        KVPairEntriesLength(kvPairs, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  // def. KVPairEntriesLength
        KVPairEntriesLength(kvPairs, 0, n);
      }
    }
  }

  lemma KVPairEntriesLengthExtend(kvPairs: Linear, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    ensures KVPairEntriesLength(kvPairs + [(key, value)], 0, |kvPairs| + 1)
         == KVPairEntriesLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
  {
    KVPairEntriesLengthPrefix(kvPairs, [(key, value)]);
  }

  lemma KVPairEntriesLengthInsert(kvPairs: Linear, insertionPoint: nat, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    requires insertionPoint <= |kvPairs|
    ensures var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
      KVPairEntriesLength(kvPairs', 0, |kvPairs'|) == KVPairEntriesLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases |kvPairs|
  {
    var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
    if |kvPairs| == insertionPoint {
      assert kvPairs' == kvPairs + [(key, value)];
      KVPairEntriesLengthExtend(kvPairs, key, value);
    } else {
      var m := |kvPairs| - 1;
      var (d0, d1) := kvPairs[m];
      var a, b, c, d := kvPairs[..insertionPoint], [(key, value)], kvPairs[insertionPoint..m], [(d0, d1)];
      assert kvPairs == a + c + d;
      assert kvPairs' == a + b + c + d;
      var ac := a + c;
      var abc := a + b + c;
      calc {
        KVPairEntriesLength(kvPairs', 0, |kvPairs'|);
        KVPairEntriesLength(abc + [(d0, d1)], 0, |abc| + 1);
      ==  { KVPairEntriesLengthExtend(abc, d0, d1); }
        KVPairEntriesLength(abc, 0, |abc|) + 4 + |d0| + |d1|;
      ==  { KVPairEntriesLengthInsert(ac, insertionPoint, key, value); }
        KVPairEntriesLength(ac, 0, |ac|) + 4 + |key| + |value| + 4 + |d0| + |d1|;
      ==  { KVPairEntriesLengthExtend(ac, d0, d1); }
        KVPairEntriesLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|;
      }
    }
  }

  /*
   * Methods that compute properties of encryption contexts
   */

  method ComputeKVPairsLength(encryptionContext: T) returns (res: nat)
    ensures res as nat == KVPairsLength(encryptionContext)
  {
    reveal ValidAAD();
    if |encryptionContext| == 0 {
      return 0;
    }

    // Iterating through a map isn't feasbile in dafny for large maps, so instead
    // convert the map to a sequence of key pairs and iterate through the sequence
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));

    var len := 2;
    var i := 0;
    while i < |kvPairs|
      invariant i <= |kvPairs|
      invariant 2 + KVPairEntriesLength(kvPairs, 0, i as int) == len as int
    {
      var kvPair := kvPairs[i];
      len := len + 4 + |kvPair.0| + |kvPair.1|;
      KVPairEntriesLengthSplit(kvPairs, 0, i + 1, |kvPairs| as int);
      i := i + 1;
    }

    assert len == 2 + KVPairEntriesLength(kvPairs, 0, |kvPairs|);
    assert len == KVPairsLength(encryptionContext);

    return len;
  }

  method ComputeValidAAD(encryptionContext: T) returns (res: bool)
    ensures res == ValidAAD(encryptionContext)
  {
    reveal ValidAAD();

    if |encryptionContext| == 0 {
      return true;
    } else if |encryptionContext| >= UINT16_LIMIT {
      return false;
    }
    
    // Iterating through a map isn't feasbile in dafny for large maps, so instead
    // convert the map to a sequence of key pairs and iterate through the sequence
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    assert forall i :: 0 <= i < |keys| ==> kvPairs[i] == (keys[i], encryptionContext[keys[i]]);

    var kvPairsLen := 2;
    var i := 0;
    while i < |kvPairs|
      invariant i <= |kvPairs|
      invariant forall k :: 0 <= k < i ==> ValidKVPair(kvPairs[k])
      invariant 2 + KVPairEntriesLength(kvPairs, 0, i as int) == kvPairsLen as int < UINT16_LIMIT
    {
      var kvPair := kvPairs[i];
      kvPairsLen := kvPairsLen + 4 + |kvPair.0| + |kvPair.1|;
      KVPairEntriesLengthSplit(kvPairs, 0, i as int + 1, |kvPairs| as int);

      // Check that AAD is still valid with this pair
      if !(|kvPair.0| < UINT16_LIMIT && |kvPair.1| < UINT16_LIMIT) {
        assert kvPair.0 in encryptionContext.Keys;
        return false; // Invalid key value pair
      } else if kvPairsLen >= UINT16_LIMIT {
        return false; // Over size limit
      }
      assert forall k :: 0 <= k < i ==> ValidKVPair(kvPairs[k]);
      assert kvPairsLen < UINT16_LIMIT;
      i := i + 1;
    }

    return true;
  }

  /*
   * Sortedness
   */

  predicate SortedKVPairsUpTo(a: Linear, n: nat)
    requires n <= |a|
  {
    forall j :: 0 < j < n ==> LexicographicLessOrEqual(a[j-1].0, a[j].0, UInt.UInt8Less)
  }

  predicate SortedKVPairs(kvPairs: Linear)
  {
    SortedKVPairsUpTo(kvPairs, |kvPairs|)
  }

  function AADToSeq(kvPairs: T): seq<uint8>
    requires ValidAAD(kvPairs)
  {
    reveal ValidAAD();
    UInt16ToSeq(KVPairsLength(kvPairs) as uint16) +
    KVPairsToSeq(kvPairs)
  }

  function KVPairsToSeq(kvPairs: T): seq<uint8>
    requires ValidKVPairs(kvPairs)
  {
    var n := |kvPairs|;
    if n == 0 then [] else
      // Defining and reasoning about order at this level is simplified by using a sequence of
      // key value pairs instead of a map.
      // Pairs are ordered lexicographically by their UTF8 encoding, which is equivalent to code
      // point ordering.
      var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence<uint8>(kvPairs.Keys, UInt.UInt8Less);
      var kvPairsSeq := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], kvPairs[keys[i]]));
      UInt16ToSeq(n as uint16) +
      KVPairEntriesToSeq(kvPairsSeq, 0, |kvPairsSeq|)
  }

  // Serialization of KVPairEntries is defined in terms of a seq of tuples, which is easier to reason about
  function KVPairEntriesToSeq(kvPairs: Linear, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires |kvPairs| < UINT16_LIMIT
    requires SortedKVPairs(kvPairs)
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else KVPairEntriesToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function KVPairToSeq(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)): seq<uint8>
    requires ValidKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  /* Function KVPairsLength is defined without referring to SerializeAAD (because then
   * these two would be mutually recursive with ValidAAD). The following lemma proves
   * that the two definitions correspond.
   */

  lemma ADDLengthCorrect(encryptionContext: T)
    requires ValidAAD(encryptionContext)
    ensures |AADToSeq(encryptionContext)| == 2 + KVPairsLength(encryptionContext)
  {
    reveal ValidAAD();
    var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    KVPairEntriesLengthCorrect(kvPairs, 0, |kvPairs|);
    /**** Here's a more detailed proof:
    var n := |kvPairs|;
    if n != 0 {
      var s := KVPairEntriesToSeq(kvPairs, 0, n);
      calc {
        |AADToSeq(kvPairs)|;
      ==  // def. AADToSeq
        |UInt16ToSeq(KVPairsLength(kvPairs) as uint16) + UInt16ToSeq(n as uint16) + s|;
      ==  // UInt16ToSeq yields length-2 sequence
        2 + 2 + |s|;
      ==  { KVPairEntriesLengthCorrect(kvPairs, 0, n); }
        2 + 2 + KVPairEntriesLength(kvPairs, 0, n);
      }
    }
    ****/
  }

  lemma KVPairEntriesLengthCorrect(encryptionContext: Linear, lo: nat, hi: nat)
    requires forall i :: 0 <= i < |encryptionContext| ==> ValidKVPair(encryptionContext[i])
    requires lo <= hi <= |encryptionContext|
    requires |encryptionContext| < UINT16_LIMIT
    requires SortedKVPairs(encryptionContext)
    ensures |KVPairEntriesToSeq(encryptionContext, lo, hi)| == KVPairEntriesLength(encryptionContext, lo, hi)
  {
    /**** Here's a more detailed proof:
    if lo < hi {
      var kvPair := kvPairs[hi - 1];
      calc {
        |KVPairEntriesToSeq(kvPairs, lo, hi)|;
      ==  // def. KVPairEntriesToSeq
        |KVPairEntriesToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPair)|;
      ==
        |KVPairEntriesToSeq(kvPairs, lo, hi - 1)| + |KVPairToSeq(kvPair)|;
      ==  { KVPairEntriesLengthCorrect(kvPairs, lo, hi - 1); }
        KVPairEntriesLength(kvPairs, lo, hi - 1) + |KVPairToSeq(kvPair)|;
      ==  // def. KVPairToSeq
        KVPairEntriesLength(kvPairs, lo, hi - 1) +
        |UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1|;
      ==
        KVPairEntriesLength(kvPairs, lo, hi - 1) + 2 + |kvPair.0| + 2 + |kvPair.1|;
      ==  // def. KVPairEntriesLength
        KVPairEntriesLength(kvPairs, lo, hi);
      }
    }
    ****/
  }
}
