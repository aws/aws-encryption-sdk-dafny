include "Definitions.dfy"
include "Utils.dfy"

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Validity {
  import opened Definitions
  import Utils

  import AlgorithmSuite
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8

  /*
   * Validity of the message header
   * The validity depends on predicates and on the types of the fields
   */
  predicate {:opaque} ValidHeaderBody(hb: HeaderBody) {
    && ValidAlgorithmID(hb.algorithmSuiteID)
    && ValidMessageId(hb.messageID)
    && ValidAAD(hb.aad)
    && ValidEncryptedDataKeys(hb.encryptedDataKeys)
    && ValidIVLength(hb.ivLength, hb.algorithmSuiteID)
    && ValidFrameLength(hb.frameLength, hb.contentType)
  }

  // TODO: strengthen spec when available
  predicate UniquelyIdentifiesMessage(id: T_MessageID)      { true }
  predicate WeaklyBindsHeaderToHeaderBody(id: T_MessageID)  { true }
  predicate EnablesSecureReuse(id: T_MessageID)             { true }
  predicate ProtectsAgainstAccidentalReuse(id: T_MessageID) { true }
  predicate ProtectsAgainstWearingOut(id: T_MessageID)      { true }

  predicate ValidMessageId(id: T_MessageID) {
    && UniquelyIdentifiesMessage(id)
    && WeaklyBindsHeaderToHeaderBody(id)
    && EnablesSecureReuse(id)
    && ProtectsAgainstAccidentalReuse(id)
    && ProtectsAgainstWearingOut(id)
  }

  predicate ValidAlgorithmID(algorithmSuiteID: AlgorithmSuite.ID) {
    algorithmSuiteID in AlgorithmSuite.Suite.Keys
  }

  predicate InBoundsKVPairsUpTo(kvPairs: EncCtx, j: nat)
    requires j <= |kvPairs|
  {
    forall i :: 0 <= i < j ==>
      && |kvPairs[i].0| < UINT16_LIMIT
      && |kvPairs[i].1| < UINT16_LIMIT
  }

  predicate InBoundsKVPairs(kvPairs: EncCtx) {
    && |kvPairs| < UINT16_LIMIT
    && InBoundsKVPairsUpTo(kvPairs, |kvPairs|)
  }

  predicate ValidKVPairs(kvPairs: EncCtx) {
    forall i :: 0 <= i < |kvPairs| ==> UTF8.ValidUTF8Seq(kvPairs[i].0) && UTF8.ValidUTF8Seq(kvPairs[i].1)
  }

  predicate {:opaque} ValidAAD(aad: T_AAD) {
    match aad
    case AAD(kvPairs) =>
      && 0 < |kvPairs|
      && InBoundsKVPairs(kvPairs)
      && ValidKVPairs(kvPairs)
      && Utils.SortedKVPairs(kvPairs)
    case EmptyAAD() => true
  }

  predicate InBoundsEncryptedDataKeysUpTo(entries: seq<EDKEntry>, j: nat)
    requires j <= |entries|
  {
    forall i :: 0 <= i < j ==> entries[i].Valid()
  }

  predicate InBoundsEncryptedDataKeys(edks: seq<EDKEntry>) {
    InBoundsEncryptedDataKeysUpTo(edks, |edks|)
  }

  predicate {:opaque} ValidEncryptedDataKeys(encryptedDataKeys: T_EncryptedDataKeys) {
    && InBoundsEncryptedDataKeys(encryptedDataKeys.entries)
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

  predicate ValidFrameLength(frameLength: uint32, contentType: T_ContentType) {
    match contentType
    case NonFramed => frameLength == 0
    case Framed => true
  }

  /*
   * Validity of the message header authentication
   */
  predicate ValidAuthenticationTag(authenticationTag: array<uint8>, tagLength: nat, iv: array<uint8>) {
    true
    // TODO: strengthen the spec
    // The algorithm suite specified by the Algorithm Suite ID field determines how the value of this field is calculated, and uses this value to authenticate the contents of the header during decryption.
  }

  predicate ValidHeaderAuthentication(ha: HeaderAuthentication, algorithmSuiteID: AlgorithmSuite.ID)
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
  {
    ValidAuthenticationTag(ha.authenticationTag, AlgorithmSuite.Suite[algorithmSuiteID].params.tagLen as nat, ha.iv)
  }
}
