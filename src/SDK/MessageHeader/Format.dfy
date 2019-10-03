include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Format {
  import AlgorithmSuite
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import UTF8

  /*
   * Definition of the message header, i.e., the header body and the header authentication
   */
  datatype Header = Header(body: HeaderBody, auth: HeaderAuthentication)
  {
    predicate Valid() {
      && body.Valid()
      && auth.Valid(body.algorithmSuiteID)
    }
  }


  /*
   * Header body type definition
   */
  const VERSION_1: uint8     := 0x01
  type Version               = x | x == VERSION_1 witness VERSION_1

  const TYPE_CUSTOMER_AED: uint8 := 0x80
  type Type                  = x | x == TYPE_CUSTOMER_AED witness TYPE_CUSTOMER_AED

  const MESSAGE_ID_LEN       := 16
  type MessageID             = x: seq<uint8> | |x| == MESSAGE_ID_LEN witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

  type Reserved              = x: seq<uint8> | x == [0,0,0,0] witness [0,0,0,0]

  datatype ContentType       = NonFramed | Framed

  function method ContentTypeToUInt8(contentType: ContentType): uint8 {
    match contentType
    case NonFramed => 0x01
    case Framed => 0x02
  }

  function method UInt8ToContentType(x: uint8): Option<ContentType> {
    if x == 0x01 then
      Some(NonFramed)
    else if x == 0x02 then
      Some(Framed)
    else
      None
  }

  lemma ContentTypeConversionsCorrect(contentType: ContentType, x: uint8)
    ensures UInt8ToContentType(ContentTypeToUInt8(contentType)) == Some(contentType)
    ensures var opt := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.get) == x
  {
  }

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Materials.EncryptedDataKey>)
  {
    predicate {:opaque} Valid() {
      && |entries| < UINT16_LIMIT
      && (forall i :: 0 <= i < |entries| ==> entries[i].Valid())
      // TODO: well-formedness of EDK
      /*
      Key Provider ID
      The key provider identifier. The value of this field indicates the provider of the encrypted data key. See Key Provider for details on supported key providers.

      Key Provider Information
      The key provider information. The key provider for this encrypted data key determines what this field contains.

      Encrypted Data Key
      The encrypted data key. It is the data key encrypted by the key provider.
      */
    }
  }

  datatype HeaderBody = HeaderBody(
                          version: Version,
                          typ: Type,
                          algorithmSuiteID: AlgorithmSuite.ID,
                          messageID: MessageID,
                          aad: Materials.EncryptionContext,
                          encryptedDataKeys: EncryptedDataKeys,
                          contentType: ContentType,
                          reserved: Reserved,
                          ivLength: uint8,
                          frameLength: uint32)
  {
    predicate {:opaque} Valid() {
      && ValidAlgorithmID(algorithmSuiteID)
      && ValidMessageID(messageID)
      && ValidAAD(aad)
      && encryptedDataKeys.Valid()
      && ValidIVLength(ivLength, algorithmSuiteID)
      && ValidFrameLength(frameLength, contentType)
    }
  }


  /*
   * Header authentication type definition
   */
  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)
  {
    predicate Valid(algorithmSuiteID: AlgorithmSuite.ID)
      requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    {
      |authenticationTag| == AlgorithmSuite.Suite[algorithmSuiteID].params.tagLen as int &&
      |iv| == AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen as int
    }
  }



  // TODO: strengthen spec when available
  predicate UniquelyIdentifiesMessage(id: MessageID)      { true }
  predicate WeaklyBindsHeaderToHeaderBody(id: MessageID)  { true }
  predicate EnablesSecureReuse(id: MessageID)             { true }
  predicate ProtectsAgainstAccidentalReuse(id: MessageID) { true }
  predicate ProtectsAgainstWearingOut(id: MessageID)      { true }

  predicate ValidMessageID(id: MessageID) {
    && UniquelyIdentifiesMessage(id)
    && WeaklyBindsHeaderToHeaderBody(id)
    && EnablesSecureReuse(id)
    && ProtectsAgainstAccidentalReuse(id)
    && ProtectsAgainstWearingOut(id)
  }

  predicate ValidAlgorithmID(algorithmSuiteID: AlgorithmSuite.ID) {
    algorithmSuiteID in AlgorithmSuite.Suite.Keys
  }

  predicate ValidKVPair(kvPair: (seq<uint8>, seq<uint8>)) {
    && |kvPair.0| < UINT16_LIMIT
    && |kvPair.1| < UINT16_LIMIT
    && UTF8.ValidUTF8Seq(kvPair.0)
    && UTF8.ValidUTF8Seq(kvPair.1)
  }

  function KVPairsLength(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): nat
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then 0 else
      KVPairsLength(kvPairs, lo, hi - 1) +
      2 + |kvPairs[hi - 1].0| +
      2 + |kvPairs[hi - 1].1|
  }

  lemma KVPairsLengthSplit(kvPairs: Materials.EncryptionContext, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |kvPairs|
    ensures KVPairsLength(kvPairs, lo, hi)
         == KVPairsLength(kvPairs, lo, mid) + KVPairsLength(kvPairs, mid, hi)
  {
  }

  lemma KVPairsLengthPrefix(kvPairs: Materials.EncryptionContext, more: Materials.EncryptionContext)
    ensures KVPairsLength(kvPairs + more, 0, |kvPairs|) == KVPairsLength(kvPairs, 0, |kvPairs|)
  {
    var n := |kvPairs|;
    if n == 0 {
    } else {
      var last := kvPairs[n - 1];
      calc {
        KVPairsLength(kvPairs + more, 0, n);
      ==  // def. KVPairsLength
        KVPairsLength(kvPairs + more, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs + more == kvPairs[..n - 1] + ([last] + more); }
        KVPairsLength(kvPairs[..n - 1] + ([last] + more), 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { KVPairsLengthPrefix(kvPairs[..n - 1], [last] + more); }
        KVPairsLength(kvPairs[..n - 1], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { KVPairsLengthPrefix(kvPairs[..n - 1], [last] + more); }
        KVPairsLength(kvPairs[..n - 1] + [last], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  { assert kvPairs[..n - 1] + [last] == kvPairs; }
        KVPairsLength(kvPairs, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==  // def. KVPairsLength
        KVPairsLength(kvPairs, 0, n);
      }
    }
  }

  lemma KVPairsLengthExtend(kvPairs: Materials.EncryptionContext, key: seq<uint8>, value: seq<uint8>)
    ensures KVPairsLength(kvPairs + [(key, value)], 0, |kvPairs| + 1)
         == KVPairsLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
  {
    KVPairsLengthPrefix(kvPairs, [(key, value)]);
  }

  lemma KVPairsLengthInsert(kvPairs: Materials.EncryptionContext, insertionPoint: nat, key: seq<uint8>, value: seq<uint8>)
    requires insertionPoint <= |kvPairs|
    ensures var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
      KVPairsLength(kvPairs', 0, |kvPairs'|) == KVPairsLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases |kvPairs|
  {
    var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
    if |kvPairs| == insertionPoint {
      assert kvPairs' == kvPairs + [(key, value)];
      KVPairsLengthExtend(kvPairs, key, value);
    } else {
      var m := |kvPairs| - 1;
      var (d0, d1) := kvPairs[m];
      var a, b, c, d := kvPairs[..insertionPoint], [(key, value)], kvPairs[insertionPoint..m], [(d0, d1)];
      assert kvPairs == a + c + d;
      assert kvPairs' == a + b + c + d;
      var ac := a + c;
      var abc := a + b + c;
      calc {
        KVPairsLength(kvPairs', 0, |kvPairs'|);
        KVPairsLength(abc + [(d0, d1)], 0, |abc| + 1);
      ==  { KVPairsLengthExtend(abc, d0, d1); }
        KVPairsLength(abc, 0, |abc|) + 4 + |d0| + |d1|;
      ==  { KVPairsLengthInsert(ac, insertionPoint, key, value); }
        KVPairsLength(ac, 0, |ac|) + 4 + |key| + |value| + 4 + |d0| + |d1|;
      ==  { KVPairsLengthExtend(ac, d0, d1); }
        KVPairsLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|;
      }
    }
  }

  function AADLength(kvPairs: Materials.EncryptionContext): nat {
    if |kvPairs| == 0 then 0 else
      2 + KVPairsLength(kvPairs, 0, |kvPairs|)
  }

  predicate {:opaque} ValidAAD(kvPairs: Materials.EncryptionContext) {
    && |kvPairs| < UINT16_LIMIT
    && (forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i]))
    && SortedKVPairs(kvPairs)
    && AADLength(kvPairs) < UINT16_LIMIT
  }

  predicate ValidIVLength(ivLength: uint8, algorithmSuiteID: AlgorithmSuite.ID) {
    algorithmSuiteID in AlgorithmSuite.Suite.Keys && AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen == ivLength
  }

  predicate ValidFrameLength(frameLength: uint32, contentType: ContentType) {
    match contentType
    case NonFramed => frameLength == 0
    case Framed => true
  }

  predicate SortedKVPairsUpTo(a: seq<(seq<uint8>, seq<uint8>)>, n: nat)
    requires n <= |a|
  {
    forall j :: 0 < j < n ==> LexicographicLessOrEqual(a[j-1].0, a[j].0, UInt8Less)
  }

  predicate SortedKVPairs(a: seq<(seq<uint8>, seq<uint8>)>)
  {
    SortedKVPairsUpTo(a, |a|)
  }

  method InsertNewEntry(kvPairs: seq<(seq<uint8>, seq<uint8>)>, key: seq<uint8>, value: seq<uint8>)
      returns (res: Option<seq<(seq<uint8>, seq<uint8>)>>, ghost insertionPoint: nat)
    requires SortedKVPairs(kvPairs)
    ensures match res
    case None =>
      exists i :: 0 <= i < |kvPairs| && kvPairs[i].0 == key  // key already exists
    case Some(kvPairs') =>
      && insertionPoint <= |kvPairs|
      && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]
      && SortedKVPairs(kvPairs')
  {
    var n := |kvPairs|;
    while 0 < n && LexicographicLessOrEqual(key, kvPairs[n - 1].0, UInt8Less)
      invariant 0 <= n <= |kvPairs|
      invariant forall i :: n <= i < |kvPairs| ==> LexicographicLessOrEqual(key, kvPairs[i].0, UInt8Less)
    {
      n := n - 1;
    }
    if 0 < n && kvPairs[n - 1].0 == key {
      return None, n;
    } else {
      var kvPairs' := kvPairs[..n] + [(key, value)] + kvPairs[n..];
      if 0 < n {
        LexPreservesTrichotomy(kvPairs'[n - 1].0, kvPairs'[n].0, UInt8Less);
      }
      return Some(kvPairs'), n;
    }
  }
}
