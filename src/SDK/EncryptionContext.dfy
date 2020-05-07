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

  type Map = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

  /*
   * Serializability predicates
   */

  predicate {:opaque} Serializable(encryptionContext: Map) {
    && SerializableKVPairs(encryptionContext)
    && Length(encryptionContext) < UINT16_LIMIT
  }

  predicate method SerializableKVPairs(encryptionContext: Map) {
    && |encryptionContext| < UINT16_LIMIT
    && (forall key :: key in encryptionContext.Keys ==> SerializableKVPair((key, encryptionContext[key])))
  }

  predicate method SerializableKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)) {
    && |kvPair.0| < UINT16_LIMIT
    && |kvPair.1| < UINT16_LIMIT
    && UTF8.ValidUTF8Seq(kvPair.0)
    && UTF8.ValidUTF8Seq(kvPair.1)
  }

  /*
   * Length properties
   */

  function Length(encryptionContext: Map): nat
  {
    if |encryptionContext| == 0 then 0 else
      // Defining and reasoning about order at this level is simplified by using a sequence of
      // key value pairs instead of a map.
      var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
      var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
      2 + LinearLength(kvPairs, 0, |kvPairs|)
  }

  /*
   * Encryption context as a sequence
   */

  // To make verification and working with iterating through the encryption context
  // simpler, here we define a specific type to represent a sequence of key-value tuples.
  type Linear = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  // Length of KVPairEntries is defined in terms of a seq of tuples, which is easier to reason about
  function LinearLength(kvPairs: Linear, lo: nat, hi: nat): nat
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then 0 else
      LinearLength(kvPairs, lo, hi - 1) +
      2 + |kvPairs[hi - 1].0| +
      2 + |kvPairs[hi - 1].1|
  }

  // There isn't an efficient way to build a map from a sequence in dafny, so this
  // extern is used specifically to convert a sequence of key value pairs to a map
  method {:extern "LinearToMap"} LinearToMap(kvPairs: Linear) returns (res: Map)

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

  function LinearToMapFunc(sequence: seq<uint8>): Result<Map>
  {
    if |sequence| < 2 then 
      Failure("to small")
    else 
      SeqToMap(sequence[2..])
  }
  
  function SeqToMap(sequence: seq<uint8>): Result<Map>
  {
    if |sequence| < 2 then 
      Failure("to small")
    else 
      var res := SeqToLinear(sequence[2..]);
      if res.Success? then Success(LinearInMap(res.value)) else Failure("to small")
  }
  
  function LinearInMap(linear: Linear): Map
  {
    if linear == [] then map[] else
      LinearInMap(linear[1..])[linear[0].0 := linear[0].1]
  }

  function InsertPair (p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear): (ls: Linear)
    requires LinearSorted(ps)
    ensures forall i :: (i in ps || i == p) <==> i in ls
    ensures LinearSorted(ls)
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less) then
        
        [p] + ps
    else
      LexIsTotal(p.0, ps[0].0, UInt.UInt8Less);
      var tail := InsertPair(p,ps[1..]);
     
      [ps[0]] + tail
  }

  function SeqToLinear(sequence: seq<uint8>): Result<Linear>
    ensures var res := SeqToLinear(sequence);
      res.Success? ==> LinearSorted(res.value)
  {
    if sequence == [] then Success([]) else
      var resHead := SeqToKVPair(sequence);
      if resHead.Success? then 
        var resTail: Result<Linear> := SeqToLinear(resHead.value.1);
        if resTail.Success? then
          Success(InsertPair(resHead.value.0, resTail.value))
        else
          Failure("too short")
      else
        Failure("Too short")
  }

  function SeqToKVPair(sequence: seq<uint8>): (res: Result<((UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), seq<uint8>)>)
    ensures
        (|sequence| >= 2
        && var kvp0Length := SeqToUInt16(sequence[..2])  as int;
        |sequence| >= 4 + kvp0Length
        && var kvp1Length := SeqToUInt16(sequence[2 + kvp0Length..4 + kvp0Length])  as int;
        |sequence| >= 4 + kvp0Length + kvp1Length
        && var kvp0 := sequence[2..2 + kvp0Length];
        var kvp1 := sequence[4 + kvp0Length..4 + kvp0Length + kvp1Length];
        UTF8.ValidUTF8Seq(kvp0) && UTF8.ValidUTF8Seq(kvp1))
      <==>
        res.Success?
    ensures match res 
      case Success(((key, value), rem)) =>
        |key| == SeqToUInt16(sequence[..2])  as int
        && key == sequence[2..2 + |key|]
        && |value| == SeqToUInt16(sequence[2 + |key|..4 + |key|])  as int
        && value == sequence[4 + |key|..4 + |key| + |value|]
        && rem == sequence[|key| + |value| + 4..]
      case Failure(_) =>
        true
  {
    if |sequence| >= 2 then
      var kvp0Length := SeqToUInt16(sequence[..2])  as int;
      if |sequence| >= kvp0Length + 4 then
        var kvp1Length := SeqToUInt16(sequence[2 + kvp0Length..4 + kvp0Length])  as int;
        if |sequence| >= kvp0Length + kvp1Length + 4 then
          var kvp0 := sequence[2..2 + kvp0Length];
          var kvp1 := sequence[4 + kvp0Length..4 + kvp0Length + kvp1Length];
          if UTF8.ValidUTF8Seq(kvp0) && UTF8.ValidUTF8Seq(kvp1) then
            var kvp0UTF: UTF8.ValidUTF8Bytes := kvp0;
            var kvp1UTF: UTF8.ValidUTF8Bytes := kvp1;
            Success(((kvp0UTF, kvp1UTF), sequence[kvp0Length + kvp1Length + 4..]))
          else
            Failure("sequence is maleformed")
        else
          Failure("out of bounds")
      else
        Failure("out of bounds")
    else
      Failure("out of bounds")
  }

  function MapToLinear(kvPairs: Map): seq<uint8>
    requires Serializable(kvPairs)
  {
    reveal Serializable();
    UInt16ToSeq(Length(kvPairs) as uint16) +
    MapToSeq(kvPairs)
  }

  function MapToSeq(kvPairs: Map): seq<uint8>
    requires SerializableKVPairs(kvPairs)
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
    requires forall i :: 0 <= i < |kvPairs| ==> SerializableKVPair(kvPairs[i])
    requires |kvPairs| < UINT16_LIMIT
    requires LinearSorted(kvPairs)
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else LinearToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function KVPairToSeq(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)): seq<uint8>
    requires SerializableKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  /* Function Length is defined without referring to SerializeAAD (because then
   * these two would be mutually recursive with Valid). The following lemma proves
   * that the two definitions correspond.
   */

  lemma LengthCorrect(encryptionContext: Map)
    requires Serializable(encryptionContext)
    ensures |MapToLinear(encryptionContext)| == 2 + Length(encryptionContext)
  {
    reveal Serializable();
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
