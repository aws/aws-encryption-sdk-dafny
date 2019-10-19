include "AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "Materials.dfy"
include "../Util/UTF8.dfy"

module MessageHeader {
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
      && |auth.iv| == body.algorithmSuiteID.IVLength()
      && |auth.authenticationTag| == body.algorithmSuiteID.TagLength()
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

  const Reserved: seq<uint8> := [0,0,0,0]

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
    predicate Valid() {
      && 0 < |entries| < UINT16_LIMIT
      && (forall i :: 0 <= i < |entries| ==> entries[i].Valid())
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
                          ivLength: uint8,
                          frameLength: uint32)
  {
    predicate Valid() {
      && ValidAAD(aad)
      && encryptedDataKeys.Valid()
      && algorithmSuiteID.IVLength() == ivLength as nat
      && ValidFrameLength(frameLength, contentType)
    }
  }

  /*
   * Header authentication type definition
   */

  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)

  /*
   * Validity predicates -- predicates that say when the data structures above are in a good state.
   */

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

  predicate ValidFrameLength(frameLength: uint32, contentType: ContentType) {
    match contentType
    case NonFramed => frameLength == 0
    case Framed => frameLength != 0
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

  /*
   * Specifications of serialized format
   */

  function {:opaque} HeaderBodyToSeq(hb: HeaderBody): seq<uint8>
    requires hb.Valid()
  {
    [hb.version as uint8] +
    [hb.typ as uint8] +
    UInt16ToSeq(hb.algorithmSuiteID as uint16) +
    hb.messageID +
    AADToSeq(hb.aad) +
    EDKsToSeq(hb.encryptedDataKeys) +
    [ContentTypeToUInt8(hb.contentType)] +
    Reserved +
    [hb.ivLength] +
    UInt32ToSeq(hb.frameLength)
  }

  function AADToSeq(kvPairs: Materials.EncryptionContext): seq<uint8>
    requires ValidAAD(kvPairs)
  {
    reveal ValidAAD();
    UInt16ToSeq(AADLength(kvPairs) as uint16) +
    var n := |kvPairs|;
    if n == 0 then [] else
      UInt16ToSeq(n as uint16) +
      KVPairsToSeq(kvPairs, 0, n)
  }

  function KVPairsToSeq(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else KVPairsToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function KVPairToSeq(kvPair: (seq<uint8>, seq<uint8>)): seq<uint8>
    requires ValidKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  function EDKsToSeq(encryptedDataKeys: EncryptedDataKeys): seq<uint8>
    requires encryptedDataKeys.Valid()
  {
    var n := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) +
    EDKEntriesToSeq(encryptedDataKeys.entries, 0, n)
  }

  function EDKEntriesToSeq(entries: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
  {
    if lo == hi then [] else EDKEntriesToSeq(entries, lo, hi - 1) + EDKEntryToSeq(entries[hi - 1])
  }

  function EDKEntryToSeq(edk: Materials.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
  {
    UInt16ToSeq(|edk.providerID| as uint16)   + StringToByteSeq(edk.providerID) +
    UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo +
    UInt16ToSeq(|edk.ciphertext| as uint16)   + edk.ciphertext
  }

  /* Function AADLength is defined without referring to SerializeAAD (because then
   * these two would be mutually recursive with ValidAAD). The following lemma proves
   * that the two definitions correspond.
   */

  lemma ADDLengthCorrect(kvPairs: Materials.EncryptionContext)
    requires ValidAAD(kvPairs)
    ensures |AADToSeq(kvPairs)| == 2 + AADLength(kvPairs)
  {
    reveal ValidAAD();
    KVPairsLengthCorrect(kvPairs, 0, |kvPairs|);
    /**** Here's a more detailed proof:
    var n := |kvPairs|;
    if n != 0 {
      var s := KVPairsToSeq(kvPairs, 0, n);
      calc {
        |AADToSeq(kvPairs)|;
      ==  // def. AADToSeq
        |UInt16ToSeq(AADLength(kvPairs) as uint16) + UInt16ToSeq(n as uint16) + s|;
      ==  // UInt16ToSeq yields length-2 sequence
        2 + 2 + |s|;
      ==  { KVPairsLengthCorrect(kvPairs, 0, n); }
        2 + 2 + KVPairsLength(kvPairs, 0, n);
      }
    }
    ****/
  }

  lemma KVPairsLengthCorrect(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat)
    requires forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
    ensures |KVPairsToSeq(kvPairs, lo, hi)| == KVPairsLength(kvPairs, lo, hi)
  {
    /**** Here's a more detailed proof:
    if lo < hi {
      var kvPair := kvPairs[hi - 1];
      calc {
        |KVPairsToSeq(kvPairs, lo, hi)|;
      ==  // def. KVPairsToSeq
        |KVPairsToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPair)|;
      ==
        |KVPairsToSeq(kvPairs, lo, hi - 1)| + |KVPairToSeq(kvPair)|;
      ==  { KVPairsLengthCorrect(kvPairs, lo, hi - 1); }
        KVPairsLength(kvPairs, lo, hi - 1) + |KVPairToSeq(kvPair)|;
      ==  // def. KVPairToSeq
        KVPairsLength(kvPairs, lo, hi - 1) +
        |UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1|;
      ==
        KVPairsLength(kvPairs, lo, hi - 1) + 2 + |kvPair.0| + 2 + |kvPair.1|;
      ==  // def. KVPairsLength
        KVPairsLength(kvPairs, lo, hi);
      }
    }
    ****/
  }
}
