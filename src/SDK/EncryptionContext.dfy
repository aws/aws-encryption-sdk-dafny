// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Util/UTF8.dfy"
include "../Util/Sets.dfy"
include "Serialize/SerializableTypes.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "EncryptionContext"} EncryptionContext {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Sets
  import opened SerializableTypes
  import Aws.Crypto

  /*
   * The main type of encryption context
   */

  type Map = Crypto.EncryptionContext
  type Linear = SerializableTypes.Linear

  /*
   * Serializability predicates
   */

  // TODO: We turned this into a function method; we should investigate
  // whether there are any performance implications
  predicate method {:opaque} Serializable(encryptionContext: Map) {
    && SerializableKVPairs(encryptionContext)
    && Length(encryptionContext) < UINT16_LIMIT
  }

  lemma LemmaESDKEncryptionContextIsSerializable(ec: SerializableTypes.ESDKEncryptionContext)
    ensures Serializable(ec)
  {
    reveal Serializable();
  }
  lemma LemmaSerializableIsESDKEncryptionContext(ec: Crypto.EncryptionContext)
    requires Serializable(ec)
    ensures IsESDKEncryptionContext(ec)
  {
    reveal Serializable();
  }

  predicate method SerializableKVPairs(encryptionContext: Map) {
    && |encryptionContext| < UINT16_LIMIT
    && (forall key :: key in encryptionContext.Keys ==> SerializableKVPair((key, encryptionContext[key])))
  }

  lemma LemmaESDKEncryptionContextIsSerializableKVPairs(ec: SerializableTypes.ESDKEncryptionContext)
    ensures SerializableKVPairs(ec)
  {
  }

  predicate method SerializableKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)) {
    && |kvPair.0| < UINT16_LIMIT
    && |kvPair.1| < UINT16_LIMIT
    && UTF8.ValidUTF8Seq(kvPair.0)
    && UTF8.ValidUTF8Seq(kvPair.1)
  }

  predicate SerializableUnsortedLinear(linear: Linear)
  {
    && |linear| < UINT16_LIMIT
    && (forall i :: 0 <= i < |linear| ==> SerializableKVPair(linear[i]))
    && LinearIsUnique(linear)
  }

  predicate SerializableLinear(linear: Linear)
  {
    && LinearSorted(linear)
    && SerializableUnsortedLinear(linear)
  }

  predicate LinearIsUnique(linear: Linear)
  {
    forall i, j | 0 <= i < j < |linear| :: linear[i].0 != linear[j].0
  }

  // There isn't an efficient way to build a map from a sequence in dafny, so this
  // extern is used specifically to convert a sequence of key value pairs to a map
  method {:extern "LinearToMap"} LinearToMap(kvPairs: Linear) returns (res: Map)
    ensures reveal Serializable(); Serializable(res) && SerializableLinear(kvPairs) ==> // If the result is a map we can serialize
      MapToSeq(res) == if |res| == 0 then [] else // then this function is the dual of MapToLinear
         UInt16ToSeq(|kvPairs| as uint16) + LinearToSeq(kvPairs, 0, |kvPairs|)

  /*
   * Useful lemmas about key-value pairs
   */

  lemma LinearSplit(kvPairs: Linear, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |kvPairs|
    ensures LinearLength(kvPairs, lo, hi)
         == LinearLength(kvPairs, lo, mid) + LinearLength(kvPairs, mid, hi)
  {
  }

  lemma LinearPrefix(kvPairs: Linear, more: Linear)
    ensures LinearLength(kvPairs + more, 0, |kvPairs|) == LinearLength(kvPairs, 0, |kvPairs|)
  {
    var n := |kvPairs|;
    if n == 0 {
    } else {
      var last := kvPairs[n - 1];
      calc {
        LinearLength(kvPairs + more, 0, n);
      ==  // def. LinearLength
        LinearLength(kvPairs + more, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs + more == kvPairs[..n - 1] + ([last] + more); }
        LinearLength(kvPairs[..n - 1] + ([last] + more), 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { LinearPrefix(kvPairs[..n - 1], [last] + more); }
        LinearLength(kvPairs[..n - 1], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { LinearPrefix(kvPairs[..n - 1], [last] + more); }
        LinearLength(kvPairs[..n - 1] + [last], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs[..n - 1] + [last] == kvPairs; }
        LinearLength(kvPairs, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  // def. LinearLength
        LinearLength(kvPairs, 0, n);
      }
    }
  }

  lemma LinearExtend(kvPairs: Linear, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    ensures LinearLength(kvPairs + [(key, value)], 0, |kvPairs| + 1)
         == LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
  {
    LinearPrefix(kvPairs, [(key, value)]);
  }

  lemma LinearInsert(kvPairs: Linear, insertionPoint: nat, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    requires insertionPoint <= |kvPairs|
    ensures var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
      LinearLength(kvPairs', 0, |kvPairs'|) == LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases |kvPairs|
  {
    var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
    if |kvPairs| == insertionPoint {
      assert kvPairs' == kvPairs + [(key, value)];
      LinearExtend(kvPairs, key, value);
    } else {
      var m := |kvPairs| - 1;
      var (d0, d1) := kvPairs[m];
      var a, b, c, d := kvPairs[..insertionPoint], [(key, value)], kvPairs[insertionPoint..m], [(d0, d1)];
      assert kvPairs == a + c + d;
      assert kvPairs' == a + b + c + d;
      var ac := a + c;
      var abc := a + b + c;
      calc {
        LinearLength(kvPairs', 0, |kvPairs'|);
        LinearLength(abc + [(d0, d1)], 0, |abc| + 1);
      ==  { LinearExtend(abc, d0, d1); }
        LinearLength(abc, 0, |abc|) + 4 + |d0| + |d1|;
      ==  { LinearInsert(ac, insertionPoint, key, value); }
        LinearLength(ac, 0, |ac|) + 4 + |key| + |value| + 4 + |d0| + |d1|;
      ==  { LinearExtend(ac, d0, d1); }
        LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|;
      }
    }
  }

  /*
   * Methods that compute properties of encryption contexts
   */

  method ComputeLength(encryptionContext: Map) returns (res: nat)
    ensures res as nat == Length(encryptionContext)
  {
    reveal Serializable();
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
      invariant 2 + LinearLength(kvPairs, 0, i as int) == len as int
    {
      var kvPair := kvPairs[i];
      len := len + 4 + |kvPair.0| + |kvPair.1|;
      LinearSplit(kvPairs, 0, i + 1, |kvPairs| as int);
      i := i + 1;
    }

    assert len == 2 + LinearLength(kvPairs, 0, |kvPairs|);
    assert len == Length(encryptionContext);

    return len;
  }

  method CheckSerializable(encryptionContext: Map) returns (res: bool)
    ensures res == Serializable(encryptionContext)
  {
    reveal Serializable();

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
      invariant forall k :: 0 <= k < i ==> SerializableKVPair(kvPairs[k])
      invariant 2 + LinearLength(kvPairs, 0, i as int) == kvPairsLen as int < UINT16_LIMIT
    {
      var kvPair := kvPairs[i];
      kvPairsLen := kvPairsLen + 4 + |kvPair.0| + |kvPair.1|;
      LinearSplit(kvPairs, 0, i as int + 1, |kvPairs| as int);

      // Check that AAD is still valid with this pair
      if !(|kvPair.0| < UINT16_LIMIT && |kvPair.1| < UINT16_LIMIT) {
        assert kvPair.0 in encryptionContext.Keys;
        return false; // Invalid key value pair
      } else if kvPairsLen >= UINT16_LIMIT {
        return false; // Over size limit
      }
      assert forall k :: 0 <= k < i ==> SerializableKVPair(kvPairs[k]);
      assert kvPairsLen < UINT16_LIMIT;
      i := i + 1;
    }

    return true;
  }

  /*
   * Sortedness
   */

  predicate LinearSortedUpTo(a: Linear, n: nat)
    requires n <= |a|
  {
    forall j :: 0 < j < n ==> LexicographicLessOrEqual(a[j-1].0, a[j].0, UInt.UInt8Less)
  }

  predicate LinearSorted(kvPairs: Linear)
  {
    LinearSortedUpTo(kvPairs, |kvPairs|)
  }


  predicate StrongLinearSorted(kvPairs: Linear)
  {
    forall i, j | 0 <= i < j < |kvPairs| :: LexicographicLessOrEqual(kvPairs[i].0, kvPairs[j].0, UInt.UInt8Less)
  }

  lemma LinearSortedImpliesStrongLinearSorted(ls: Linear)
    requires LinearSorted(ls);
    ensures StrongLinearSorted(ls);
  {
    if |ls| <= 1 {
      // If ls is empty it is always sorted
    } else {
      forall i, j | 0 <= i < j < |ls|
        ensures LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less)
      {
        //Induction on i;
        LinearSortedImpliesStrongLinearSorted(ls[1..]);
        if i == 0 && 2 <= |ls| {
          LexIsReflexive(ls[1].0, UInt.UInt8Less);
          LexIsTransitive(ls[i].0, ls[1].0, ls[j].0, UInt.UInt8Less);
          assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
        } else {
          assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
        }
      }
    }
  }

  // Proof that two sorted sequences with unique elements are the same if they contain the same elements
  lemma SortedSequenceIsUnqiue(xs: Linear, ys: Linear)
    requires LinearSorted(xs) && LinearIsUnique(xs)
    requires LinearSorted(ys) && LinearIsUnique(ys)
    requires forall p :: p in xs <==> p in ys;
    ensures xs == ys
  {
    LinearSortedImpliesStrongLinearSorted(xs); // Convert sorted to stronger definition
    LinearSortedImpliesStrongLinearSorted(ys);

    if xs != [] && ys != [] { // If the lists are not empty
      assert xs[0] == ys[0] by { // Then the heads are the same
        if xs[0] != ys[0] { // Proof by contradiction
          assert forall p | p in xs[1..] :: LexicographicLessOrEqual(xs[0].0, p.0, UInt.UInt8Less); // We know the head is the smallest element
          assert xs[0] in ys[1..] by { // So the smallest element of xs is in the tail of ys
            assert xs[0] != ys[0] && !(xs[0] in ys[1..]) ==> xs[0] !in ys;
          }

          assert forall p | p in ys[1..] :: LexicographicLessOrEqual(ys[0].0, p.0, UInt.UInt8Less); // Same for the head of ys
          assert ys[0] in xs[1..] by {
            assert ys[0] != xs[0] && !(ys[0] in xs[1..]) ==> ys[0] !in xs;
          }

          assert LexicographicLessOrEqual(ys[0].0, xs[0].0, UInt.UInt8Less); // So the smallest element of ys is smaller equal the smallest element of ys
          assert LexicographicLessOrEqual(xs[0].0, ys[0].0, UInt.UInt8Less); // The same the other way arround
          assert false; //We assumed xs[0] != ys[0] so we arrive at a contradiction
        }
      }

      // Use structural induction on the tail
      assert forall p :: p in xs[1..] <==> p in ys[1..] by { // Proof Pre-conditions are maintained
        if exists p :: p in xs[1..] && ! (p in ys[1..]) { // If the Pre-condition does not hold then there exist an elemnt in the tail of xs which is not in ys
          var p :| p in xs[1..] && !(p in ys[1..]);
          assert p != ys[0]; // Then this elemnt is not equal to the head of ys since all elements are unqiue
          assert p in xs && !(p in ys);
          assert false; // Then this element also does not exist in ys so we arrive at a contradiction
        } else {
          if exists p :: p in ys[1..] && ! (p in xs[1..]) {// Same but with xs and ys switched which covers all cases
            var p :| p in ys[1..] && !(p in xs[1..]);
            assert p != xs[0];
            assert p in xs && !(p in ys);
            assert false;
          }
        }
      }
      SortedSequenceIsUnqiue(xs[1..], ys[1..]); // Step

    } else { // If one of the list is empty then both are empty or we arrive at a trivial contradiction
      if xs == [] && ys != [] {
        assert ys[0] in xs;
        assert false;
      }
      if ys == [] && xs != [] {
        assert xs[0] in ys;
        assert false;
      }
    }
  }

  /**
   * Definition of dual DeserializeAAD
   */

  predicate LinearSeqToMap(sequence: seq<uint8>, resultMap: ESDKEncryptionContext)
  {
    if 2 <= |sequence| && |sequence[2..]| < UINT16_LIMIT then
      sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16) && SeqToMap(sequence[2..], resultMap)
    else
      false
  }


  // Deserialization is a surjection. This predicate holds if a sequence can be deserialized to the result map
  predicate SeqToMap(sequence: seq<uint8>, resultMap: ESDKEncryptionContext)
  {
    if 2 <= |sequence| then
      exists unsortedKvPairs :: SeqToLinearToMap(sequence, resultMap, unsortedKvPairs, InsertionSort(unsortedKvPairs))
    else
      |resultMap| == 0
  }

  predicate SeqToLinearToMap(sequence: seq<uint8>, resultMap: ESDKEncryptionContext, unsortedKvPairs: Linear, sortedKvPairs: Linear)
  {
    && 2 <= |sequence| // All inputs have a valid form
    && SerializableUnsortedLinear(unsortedKvPairs)
    && SerializableLinear(sortedKvPairs)
    && SerializableKVPairs(resultMap)
    && sequence[..2] == UInt16ToSeq(|resultMap| as uint16) // The resulting map has the expected amount of KvPAirs
    && LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) == sequence[2..] // The unordered sequence of KvPairs can be deserialized to the tail of the sequence
    && sortedKvPairs == InsertionSort(unsortedKvPairs) // Then if we sort the list of kvPairs
    && MapToSeq(resultMap) == sequence[..2] + LinearToSeq(sortedKvPairs, 0, |sortedKvPairs|) // We can deserialize it such that the result is equal to the deserialization of the map  }
  }

  // Proof SerializeAAD is a subset of WeakSerializeAAD
  lemma MapToLinearIsDualLinearSeqToMap(resultMap: ESDKEncryptionContext)
    // requires Serializable(resultMap)
    ensures LinearSeqToMap(MapToLinear(resultMap), resultMap)
  {
    reveal Serializable(), MapToLinear();
    LengthCorrect(resultMap);
    MapToSeqIsDualSeqToMap(resultMap);
  }

  function LinearToUnorderedSeq(kvPairs: Linear, lo: nat, hi: nat): seq<uint8>
    requires SerializableUnsortedLinear(kvPairs)
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else LinearToUnorderedSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  // Allows induction on kvpairs for LinearToUnorderedSeq
  lemma LinearToUnorderedSeqInductiveStep(kvHead: Linear, kvTail: Linear, lo: nat, hi: nat)
    requires SerializableUnsortedLinear(kvHead + kvTail)
    requires lo <= hi <= |kvHead|
    ensures SerializableUnsortedLinear(kvHead)
    ensures LinearToUnorderedSeq(kvHead + kvTail, lo, hi) == LinearToUnorderedSeq(kvHead, lo, hi)
  {
    assert SerializableUnsortedLinear(kvHead) by {
      assert |kvHead| < UINT16_LIMIT;
      assert forall i :: 0 <= i < |kvHead| ==> SerializableKVPair(kvHead[i]) by {
        assert forall pair :: pair in kvHead ==> pair in (kvHead + kvTail);
        assert (exists pair :: pair in kvHead && !SerializableKVPair(pair)) ==> (exists pair :: pair in (kvHead + kvTail) && !SerializableKVPair(pair));
      }
      assert LinearIsUnique(kvHead) by {
        var kvPairs := kvHead + kvTail;
        assert forall i | 0 <= i < |kvHead| :: kvHead[i] == kvPairs[i];
        assert (exists i, j | 0 <= i < j < |kvHead| :: kvHead[i] == kvHead[j]) ==>
          (exists i, j | 0 <= i < j < |kvPairs| :: kvPairs[i] == kvPairs[j]);
      }
    }
  }

  lemma MapToSeqIsDualSeqToMap(resultMap: ESDKEncryptionContext)
    requires SerializableKVPairs(resultMap)
    ensures SeqToMap(MapToSeq(resultMap), resultMap)
  {
    var sequenceComplete := MapToSeq(resultMap);
    if sequenceComplete != [] { // If the sequence is not empty
      var sequence := sequenceComplete[2..];
        var kvPairs :| // Then there exists a sequence of kvPairs which is deserialized to the output sequence of LinearToSeq
          && (forall i :: 0 <= i < |kvPairs| ==> SerializableKVPair(kvPairs[i]))
          && |kvPairs| < UINT16_LIMIT
          && LinearSorted(kvPairs)
          && LinearIsUnique(kvPairs)
          && LinearToSeq(kvPairs, 0, |kvPairs|) == sequence
          && sequenceComplete[..2] == UInt16ToSeq(|kvPairs| as uint16);

      InsertionSortPreservesProperties(kvPairs); // We can sort the kvPairs which preserves all properties of the kvPairs
      SortedSequenceIsUnqiue(kvPairs, InsertionSort(kvPairs)); // Two sorted sequences with unique elements are the same
      SortedLinearIsFixpointAADDuality(kvPairs); // And the weak and strong deserialization return the same value for sorted sequences
      // From this we can conclude that SeqToMap hold (intuitively this is true since LinearToSeq and LiniearToUnordered seq are the same on ordered inputs)
    } else {
      // Trivial case
    }
  }

  lemma SortedLinearIsFixpointAADDuality(linear: Linear)
    requires forall p | p in linear :: SerializableKVPair(p)
    requires |linear| < UINT16_LIMIT
    requires LinearIsUnique(linear)
    requires LinearSorted(linear)
    ensures forall hi | 0 <= hi <= |linear| :: LinearToUnorderedSeq(linear, 0, hi) == LinearToSeq(linear, 0, hi)
  {
    SortedLinearIsFixpointAADDualityAux(linear, |linear|);
  }

  lemma SortedLinearIsFixpointAADDualityAux(linear: Linear, lim: nat)
    requires forall p | p in linear :: SerializableKVPair(p)
    requires |linear| < UINT16_LIMIT
    requires LinearIsUnique(linear)
    requires LinearSorted(linear)
    requires lim <= |linear|
    ensures forall hi | 0 <= hi <= lim :: LinearToUnorderedSeq(linear, 0, hi) == LinearToSeq(linear, 0, hi)
  {
    if lim == 0 {
      assert LinearToUnorderedSeq(linear, 0, 0) == LinearToSeq(linear, 0, 0);
    } else {
      SortedLinearIsFixpointAADDualityAux(linear, lim - 1);
      assert LinearToUnorderedSeq(linear, 0, lim) == LinearToSeq(linear, 0, lim);
    }
  }

  // Lemma shows sorting preserves properties of ps
  lemma InsertionSortPreservesProperties(ps: Linear)
    requires LinearIsUnique(ps)
    requires forall l | l in ps :: SerializableKVPair(l)
    ensures LinearIsUnique(InsertionSort(ps))
    ensures forall l | l in InsertionSort(ps) :: SerializableKVPair(l)
    ensures |InsertionSort(ps)| == |ps|
  {
    if ps == [] {
      // Trivial base case
    } else { // Inductive step
      var ls := InsertionSort(ps[1..]);
      forall j | 0 <= j < |ls| // Proof that ps[0] is not contained in the sorted ps[1..]
        ensures ps[0].0 != ls[j].0
      {
        assert ps[0].0 == ls[j].0 ==> ls[j] in ps[1..];
        assert ps[0].0 == ls[j].0 ==> false;
      }
      InsertPairPreservesProperties(ps[0], ls);
    }
  }

  // Lemma shows that inserting preserves properties of p and ps
  lemma InsertPairPreservesProperties(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear)
    requires LinearSorted(ps)
    requires LinearIsUnique(ps)
    requires forall j | 0 <= j < |ps| :: p.0 != ps[j].0
    requires forall l | l in ps :: SerializableKVPair(l)
    requires SerializableKVPair(p);
    ensures LinearIsUnique( InsertPair(p, ps))
    ensures forall l | l in InsertPair(p, ps) :: SerializableKVPair(l)
    ensures |InsertPair(p, ps)| == |ps| + 1
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less){

    } else {
      assert LinearIsUnique([ps[0]] + InsertPair(p, ps[1..])) by {
        var ls := InsertPair(p, ps[1..]);
        var l := ps[0];
        assert !LinearIsUnique([l] + ls) ==> exists m | m in ls :: m.0 == l.0;
      }
    }
  }

  /**
   * Definition SerializeAAD
   */
  function MapToSeq(kvPairs: ESDKEncryptionContext): seq<uint8>
    // requires SerializableKVPairs(kvPairs)
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
      LinearToSeq(kvPairsSeq, 0, |kvPairsSeq|)
  }

  // Serialization of KVPairEntries is defined in terms of a seq of tuples, which is easier to reason about
  function LinearToSeq(kvPairs: Linear, lo: nat, hi: nat): seq<uint8>
    requires SerializableLinear(kvPairs)
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else LinearToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function {:opaque} MapToLinear(kvPairs: ESDKEncryptionContext): seq<uint8>
    // requires Serializable(kvPairs)
  {
    // reveal Serializable();
    UInt16ToSeq(Length(kvPairs) as uint16) +
    MapToSeq(kvPairs)
  }

  function KVPairToSeq(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)): seq<uint8>
    requires SerializableKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  function InsertionSort(linear: Linear): Linear
    ensures var linearSorted := InsertionSort(linear);
      (forall p :: p in linear <==> p in linearSorted)
      && LinearSorted(linearSorted)
  {
    if linear == [] then [] else InsertPair(linear[0], InsertionSort(linear[1..]))
  }

  function InsertPair(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear): Linear
    requires LinearSorted(ps)
    ensures var ls := InsertPair(p, ps);
      LinearSorted(ls)
      && forall l :: (l in ps || l == p) <==> l in ls
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less) then
      [p] + ps
    else
      LexIsTotal(p.0, ps[0].0, UInt.UInt8Less);
      [ps[0]] + InsertPair(p, ps[1..])
  }

  /**
   * UTF8 conversion section
   * Note: that this definition is not used needed for the verification of the MessageHeader the serialize definition is used instead
   */
  function GetUTF8(sequence: seq<uint8>, length: nat): (res: Option<UTF8.ValidUTF8Bytes>)
    ensures (|sequence| >= length && UTF8.ValidUTF8Seq(sequence[..length])) <==> res.Some?
    ensures res.Some? ==> sequence[..length] == res.value
  {
      if |sequence| >= length then
        var utfSeq := sequence[..length];
        if UTF8.ValidUTF8Seq(utfSeq) then
          var utf: UTF8.ValidUTF8Bytes  := utfSeq;
          Some(utf)
        else
          None // Invalid utf
      else
        None // out of bounds
  }

  lemma DualOfUTF8(utf: UTF8.ValidUTF8Bytes, remainder: seq<uint8>)
    requires |utf| < UINT16_LIMIT && UTF8.ValidUTF8Seq(utf)
    ensures var serializedUtf := UInt16ToSeq(|utf| as uint16) + utf + remainder;
      GetUTF8(serializedUtf[2..], |utf|) == Some(utf)
  {
    var serializedUtf := UInt16ToSeq(|utf| as uint16) + utf + remainder;
    assert serializedUtf[2..][..|utf|] == utf;
    var serial := serializedUtf[2..];
    var deserializedUTF := GetUTF8(serial, |utf|);
    // seq to UTF8 casting is not done automatically by Dafny and needs to be done manually
    assert deserializedUTF.Some? by {
      assert serial[..|utf|] == utf;
      assert |serial| >= |utf| && UTF8.ValidUTF8Seq(serial[..|utf|]);
    }
    assert deserializedUTF.value == serial[..|utf|];
  }

  /* Function Length is defined without referring to SerializeAAD (because then
   * these two would be mutually recursive with Valid). The following lemma proves
   * that the two definitions correspond.
   */
  lemma LengthCorrect(encryptionContext: ESDKEncryptionContext)
    // requires Serializable(encryptionContext)
    ensures |MapToLinear(encryptionContext)| == 2 + Length(encryptionContext)
  {
    reveal Serializable(), MapToLinear();
    var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    LinearLengthCorrect(kvPairs, 0, |kvPairs|);
    /**** Here's a more detailed proof:
    var n := |kvPairs|;
    if n != 0 {
      var s := LinearToSeq(kvPairs, 0, n);
      calc {
        |MapToLinear(kvPairs)|;
      ==  // def. MapToLinear
        |UInt16ToSeq(Length(kvPairs) as uint16) + UInt16ToSeq(n as uint16) + s|;
      ==  // UInt16ToSeq yields length-2 sequence
        2 + 2 + |s|;
      ==  { LinearLengthCorrect(kvPairs, 0, n); }
        2 + 2 + LinearLength(kvPairs, 0, n);
      }
    }
    ****/
  }

  lemma LinearLengthCorrect(encryptionContext: Linear, lo: nat, hi: nat)
    requires forall i :: 0 <= i < |encryptionContext| ==> SerializableKVPair(encryptionContext[i])
    requires lo <= hi <= |encryptionContext|
    requires |encryptionContext| < UINT16_LIMIT
    requires LinearSorted(encryptionContext)
    requires LinearIsUnique(encryptionContext)
    ensures |LinearToSeq(encryptionContext, lo, hi)| == LinearLength(encryptionContext, lo, hi)
  {
    /**** Here's a more detailed proof:
    if lo < hi {
      var kvPair := kvPairs[hi - 1];
      calc {
        |LinearToSeq(kvPairs, lo, hi)|;
      ==  // def. LinearToSeq
        |LinearToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPair)|;
      ==
        |LinearToSeq(kvPairs, lo, hi - 1)| + |KVPairToSeq(kvPair)|;
      ==  { LinearLengthCorrect(kvPairs, lo, hi - 1); }
        LinearLength(kvPairs, lo, hi - 1) + |KVPairToSeq(kvPair)|;
      ==  // def. KVPairToSeq
        LinearLength(kvPairs, lo, hi - 1) +
        |UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1|;
      ==
        LinearLength(kvPairs, lo, hi - 1) + 2 + |kvPair.0| + 2 + |kvPair.1|;
      ==  // def. LinearLength
        LinearLength(kvPairs, lo, hi);
      }
    }
    ****/
  }
}
