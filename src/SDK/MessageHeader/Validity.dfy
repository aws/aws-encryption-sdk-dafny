include "Definitions.dfy"
include "Utils.dfy"

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "../Materials.dfy"

module MessageHeader.Validity {
  import Msg = Definitions
  import Utils

  import AlgorithmSuite
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Materials

  /*
   * Validity of the message header
   * The validity depends on predicates and on the types of the fields
   */
  predicate ValidHeader(header: Msg.Header) {
    && ValidHeaderBody(header.body)
    && ValidHeaderAuthentication(header.auth, header.body.algorithmSuiteID)
  }

  predicate {:opaque} ValidHeaderBody(hb: Msg.HeaderBody) {
    && ValidAlgorithmID(hb.algorithmSuiteID)
    && ValidMessageId(hb.messageID)
    && ValidAAD(hb.aad)
    && ValidEncryptedDataKeys(hb.encryptedDataKeys)
    && ValidIVLength(hb.ivLength, hb.algorithmSuiteID)
    && ValidFrameLength(hb.frameLength, hb.contentType)
  }

  // TODO: strengthen spec when available
  predicate UniquelyIdentifiesMessage(id: Msg.MessageID)      { true }
  predicate WeaklyBindsHeaderToHeaderBody(id: Msg.MessageID)  { true }
  predicate EnablesSecureReuse(id: Msg.MessageID)             { true }
  predicate ProtectsAgainstAccidentalReuse(id: Msg.MessageID) { true }
  predicate ProtectsAgainstWearingOut(id: Msg.MessageID)      { true }

  predicate ValidMessageId(id: Msg.MessageID) {
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
    && Utils.SortedKVPairs(kvPairs)
    && AADLength(kvPairs) < UINT16_LIMIT
  }

  predicate {:opaque} ValidEncryptedDataKeys(encryptedDataKeys: Msg.EncryptedDataKeys) {
    && |encryptedDataKeys.entries| < UINT16_LIMIT
    && (forall i :: 0 <= i < |encryptedDataKeys.entries| ==> encryptedDataKeys.entries[i].Valid())
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

  predicate ValidIVLength(ivLength: uint8, algorithmSuiteID: AlgorithmSuite.ID) {
    algorithmSuiteID in AlgorithmSuite.Suite.Keys && AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen == ivLength
  }

  predicate ValidFrameLength(frameLength: uint32, contentType: Msg.ContentType) {
    match contentType
    case NonFramed => frameLength == 0
    case Framed => true
  }

  /*
   * Validity of the message header authentication
   */
  predicate ValidHeaderAuthentication(ha: Msg.HeaderAuthentication, algorithmSuiteID: AlgorithmSuite.ID)
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
  {
    |ha.authenticationTag| == AlgorithmSuite.Suite[algorithmSuiteID].params.tagLen as int &&
    |ha.iv| == AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen as int
  }
}
