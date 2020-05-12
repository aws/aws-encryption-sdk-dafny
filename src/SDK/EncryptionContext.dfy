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
      }else{
        forall i, j | 0 <= i < j < |ls| 
          ensures LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less)
        {
          //Induction on i;
          LinearSortedImpliesStrongLinearSorted(ls[1..]);
          if i == 0 && 2 <= |ls| {
            LexIsReflexive(ls[1].0, UInt.UInt8Less);
            LexIsTransitive(ls[i].0, ls[1].0, ls[j].0, UInt.UInt8Less);
            assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
          }else{
            assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
          }
        }
      }
    }

  function LinearToMapFunc(sequence: seq<uint8>): Option<Map>
  {
    if |sequence| < 2 then 
      None // too small
    else 
      SeqToMap(sequence[2..])
  }
  
  function SeqToMap(sequence: seq<uint8>): Option<Map>
  {
    if |sequence| < 2 then 
      None // Too small
    else 
      var res := SeqToLinear(sequence[2..], []);
      if res.Some? then Some(LinearInMap(res.get)) else None
  }
  
  function LinearInMap(linear: Linear): Map
  {
    if linear == [] then map[] else
      LinearInMap(linear[1..])[linear[0].0 := linear[0].1]
  }

  function InsertPair(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear): (res: (Option<Linear>, nat))
    requires LinearSorted(ps)
    ensures match res.0
    case None =>
      res.1 < |ps|
      && ps[res.1].0 == p.0  // Key already exists
    case Some(ls) =>
      && res.1 <= |ps|
      && ls == ps[..res.1] + [p] + ps[res.1..]
      && LinearSorted(ls)
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less) then
      if 0 < |ps| && p.0 == ps[0].0 then
        (None, 0) // Duplicate key
      else
        (Some([p] + ps), 0)
    else
      LexIsTotal(p.0, ps[0].0, UInt.UInt8Less);
      var res := InsertPair(p,ps[1..]);
      if res.0.Some? then
        (Some([ps[0]] + res.0.get), res.1 + 1)
      else
        (res.0, res.1 + 1)
  }

  lemma InsertFailsOnDuplicate(ls: Linear, pair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes))
    requires LinearSorted(ls)
    requires exists l | l in ls :: pair.0 == l.0
    ensures InsertPair(pair, ls).0.None?
  {
    if (ls[0].0 == pair.0) {
      LexIsReflexive(pair.0, UInt.UInt8Less);
    }else{
      InsertFailsOnDuplicate(ls[1..], pair);
      LinearSortedImpliesStrongLinearSorted(ls);
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
        if xs[0] != ys[0]{ // Proof by contradiction
          assert forall p | p in xs[1..] :: LexicographicLessOrEqual(xs[0].0, p.0, UInt.UInt8Less); // We know the head is the smallest element 
          assert xs[0] in ys[1..] by { // So the smallest element of xs is in the tail of ys
            assert xs[0] != ys[0] && !(xs[0] in ys[1..]) ==> xs[0] !in ys;
          }
        
          assert forall p | p in ys[1..] :: LexicographicLessOrEqual(ys[0].0, p.0, UInt.UInt8Less); // Same for the head of ys
          assert ys[0] in xs[1..]by {
            assert ys[0] != xs[0] && !(ys[0] in xs[1..]) ==> ys[0] !in xs;
          }
          
          assert LexicographicLessOrEqual(ys[0].0, xs[0].0, UInt.UInt8Less); // So the smallest element of ys is smaller equal the smallest element of ys
          assert LexicographicLessOrEqual(xs[0].0, ys[0].0, UInt.UInt8Less); // The same the other way arround
          assert false; //We assumed xs[0] != ys[0] so we arrive at a contradiction
        }
      }
      
      // Use structural induction on the tail
      assert forall p :: p in xs[1..] <==> p in ys[1..] by{ // Proof Pre-conditions are maintained
        if exists p :: p in xs[1..] && ! (p in ys[1..]){ // If the Pre-condition does not hold then there exist an elemnt in the tail of xs which is not in ys
          var p :| p in xs[1..] && !(p in ys[1..]);
          assert p != ys[0]; // Then this elemnt is not equal to the head of ys since all elements are unqiue
          assert p in xs && !(p in ys);
          assert false; // Then this element also does not exist in ys so we arrive at a contradiction
        }else{
          if exists p :: p in ys[1..] && ! (p in xs[1..]){// Same but with xs and ys switched which covers all cases
            var p :| p in ys[1..] && !(p in xs[1..]);
            assert p != xs[0];
            assert p in xs && !(p in ys);
            assert false;
          }
        }
      }
      SortedSequenceIsUnqiue(xs[1..], ys[1..]); // Step
      
    }else{ // If one of the list is empty then both are empty or we arrive at a trivial contradiction
      if xs == [] && ys != []{
        assert ys[0] in xs; 
        assert false;
      }
      if ys == [] && xs != []{
        assert xs[0] in ys; 
        assert false;
      }
    }
  }

  predicate LinearIsUnique(linear: Linear)
  {
    forall i, j | 0 <= i < j < |linear| :: linear[i].0 != linear[j].0
  }


  function SeqToLinear(sequence: seq<uint8>, linear: Linear): Option<Linear>
    requires LinearSorted(linear)
    requires LinearIsUnique(linear)
    ensures var res := SeqToLinear(sequence, linear);
      res.Some? ==> LinearSorted(res.get)
      && LinearIsUnique(res.get)
  {
    if sequence == [] then Some(linear) else
      var resHead := SeqToKVPair(sequence); 
      if resHead.Some? then 
        var newLinear := InsertPairMock(resHead.get.0, linear);
        if newLinear.Some? then
          SeqToLinear(resHead.get.1, newLinear.get)
        else
          None // Duplicate key
      else
        None // Too short
  }

  lemma SeqToLinearSequentialReorder(seqHead: seq<uint8>, linHead: Linear, seqTail: seq<uint8>,  linTail: Linear)
    requires SeqToLinear(seqHead, []) == Some(linHead)
    requires SeqToLinear(seqTail, []) == Some(linTail)
    ensures SeqToLinear(seqHead + seqTail, []) == SeqToLinear(seqTail + seqHead, [])
  {
    if exists p :: p in linHead && p in linTail {
      assert SeqToLinear(seqHead + seqTail, []) == SeqToLinear(seqTail, linHead) by {

      }
      assert SeqToLinear(seqTail + seqHead, []).None?;
    }else{
      
      assert SeqToLinear(seqHead + seqTail, []).Some?;
      assert SeqToLinear(seqTail + seqHead, []).Some?;
    }
  }

  // Simplified Function to get the content of Linear for proofs
  function SeqToContentOfLinear(sequence: seq<uint8>, linear: Linear): Option<Linear>
  {
     if sequence == [] then Some(linear) else
      var resHead := SeqToKVPair(sequence); 
      if resHead.Some? then 
        SeqToContentOfLinear(resHead.get.1, linear + [resHead.get.0])
      else
        None // Too short
  }

  // Links SeqToLinear with SeqToContentOfLinear
  lemma SeqToLinearContent(sequence: seq<uint8>, linear: Linear, linearSorted: Linear)
    requires LinearSorted(linearSorted) && LinearIsUnique(linearSorted)
    requires SeqToLinear(sequence, linearSorted).Some?
    requires forall p :: p in linear <==> p in linearSorted
    ensures SeqToContentOfLinear(sequence, linear).Some?
    ensures forall p :: p in SeqToContentOfLinear(sequence, linear).get <==> p in SeqToLinear(sequence, linearSorted).get
  {

  }

  lemma SeqToLinearContentIsWeaker(sequence: seq<uint8>, linear: Linear, linearSorted: Linear)
    requires LinearSorted(linearSorted) && LinearIsUnique(linearSorted)
    requires forall p :: p in linear <==> p in linearSorted
    requires SeqToLinear(sequence, linearSorted).Some?
    ensures SeqToContentOfLinear(sequence, linear).Some?
  {

  }

  lemma SeqToLinearToCall(seqHead: seq<uint8>, seqTail: seq<uint8>, linHead: Linear)
    requires SeqToLinear(seqHead, []) == Some(linHead)
    ensures SeqToLinear(seqHead + seqTail, []) == SeqToLinear(seqTail, linHead)
  {
    if linHead == [] {  
      SeqToLinearContent(seqHead, [] , []);
      assert SeqToContentOfLinear(seqHead, []) == Some([]) by {
        calc{
          forall p :: p in SeqToContentOfLinear(seqHead, []).get <==> p in SeqToLinear(seqHead, []).get;
        <==>
          forall p :: p in SeqToContentOfLinear(seqHead, []).get <==> p in Some([]).get;
        <==>
          forall p :: p in SeqToContentOfLinear(seqHead, []).get <==> p in [];
        <==>
          forall p :: !(p in SeqToContentOfLinear(seqHead, []).get);
        <==>{ var lin := SeqToContentOfLinear(seqHead, []).get;
              assert 0 < |lin| ==> lin[0] in []; }
          SeqToContentOfLinear(seqHead, []).get == [];
        <==>
          SeqToContentOfLinear(seqHead, []) == Some([]);
        }
      }

      assert seqHead == [] by {
        if seqHead == [] {

        }else{
          assert SeqToContentOfLinear(seqHead, []).Some?;
          var resHead := SeqToKVPair(seqHead);
          assert resHead.Some?;
          assert resHead.get.0 in SeqToContentOfLinear(seqHead, []).get;

        }
      }
      assert seqHead + seqTail == seqTail;
      assert SeqToLinear(seqHead + seqTail, []) == SeqToLinear(seqTail, linHead);
    } else {
      assert SeqToLinear(seqHead + seqTail, []) == SeqToLinear(seqTail, linHead);
    }
  }


  function {:axiom } InsertPairMock(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear): (res: Option<Linear>)
    requires LinearSorted(ps)
    requires LinearIsUnique(ps) 
    ensures (exists l | l in ps :: p.0 == l.0) <==> res.None?
    ensures res.Some? ==> LinearSorted(res.get) && LinearIsUnique(res.get)
    ensures res.Some? ==> forall l :: (l in ps || l == p) <==> l in res.get

  function GetUTF8(sequence: seq<uint8>, length: nat): (res: Option<UTF8.ValidUTF8Bytes>)
    ensures (|sequence| >= length && UTF8.ValidUTF8Seq(sequence[..length])) <==> res.Some?
    ensures res.Some? ==> sequence[..length] == res.get
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

  function SeqToKVPair(sequence: seq<uint8>): (res: Option<((UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), seq<uint8>)>)
  {
    if |sequence| >= 2 then
      var keyLength := SeqToUInt16(sequence[..2])  as nat;  
      var key := GetUTF8(sequence[2..], keyLength);
      if key.Some? && |sequence| >= keyLength + 4 then
        var valueLength := SeqToUInt16(sequence[keyLength + 2..keyLength + 4])  as nat;              
        var value := GetUTF8(sequence[keyLength + 4 ..], valueLength);
        if value.Some? then
          Some(((key.get, value.get), sequence[4 + keyLength + valueLength..]))
        else
          None // "Invalid utf")
      else
        None // Invalid utf or out of bounds
    else
      None // out of bounds
  }

  lemma KVPairToSeqIsDualSeqToKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), remainder: seq<uint8>)
    requires SerializableKVPair(kvPair); 
    ensures var sequence := KVPairToSeq(kvPair);
      SeqToKVPair(sequence + remainder) == Some((kvPair, remainder))
    {
      var sequence := KVPairToSeq(kvPair) + remainder;
      var deserializedPair := SeqToKVPair(sequence);

      assert deserializedPair.Some? by {
        // Prove that the two calls deserializing the utf8 don't error 
        assert UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + sequence[2 + |kvPair.0|..] == sequence;
        DualOfUTF8(kvPair.0, sequence[2 + |kvPair.0|..]);
        assert Some(kvPair.0) == GetUTF8(sequence[2..], |kvPair.0|);
        
        assert sequence[..2 + |kvPair.0|] +  UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1 + sequence[4 + |kvPair.0| + |kvPair.1 |..] == sequence;
        DualOfUTF8(kvPair.1, sequence[2 + |kvPair.0| + 2 + |kvPair.1|..]);
        assert sequence[2 + |kvPair.0|..] == UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1 + sequence[2 + |kvPair.0| + 2 + |kvPair.1|..];
        assert Some(kvPair.1) == GetUTF8(sequence[2 + |kvPair.0|..][2..], |kvPair.1|);
      }
      assert deserializedPair.get.0.0 == kvPair.0;
      assert deserializedPair.get.0.1 == kvPair.1;
      assert deserializedPair.get.1 == remainder;
         
    }

    lemma DualOfUTF8(utf: UTF8.ValidUTF8Bytes, remainder: seq<uint8>)
      requires |utf| < UINT16_LIMIT && UTF8.ValidUTF8Seq(utf)
      ensures var serializedUtf := UInt16ToSeq(|utf| as uint16) + utf + remainder;
        GetUTF8(serializedUtf[2..], |utf|) == Some(utf) 
    {
      var serializedUtf := UInt16ToSeq(|utf| as uint16) + utf + remainder;
      var serial := serializedUtf[2..];
      var deserializedUTF := GetUTF8(serial, |utf|);
      // seq to UTF8 casting is not done automatically by Dafny and needs to be done manually
      assert deserializedUTF.Some? by {
        assert serial[..|utf|] == utf;
        assert |serial| >= |utf| && UTF8.ValidUTF8Seq(serial[..|utf|]);
      }
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
