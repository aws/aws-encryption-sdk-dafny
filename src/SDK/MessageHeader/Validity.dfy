include "Definitions.dfy"
include "Utils.dfy"

include "../AlgorithmSuite.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Validity {
    import opened Definitions
    import opened Utils

    import AlgorithmSuite
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened UTF8
    /*
     * Validity of the message header
     * The validity depends on predicates and on the types of the fields
     */
    predicate {:opaque} ValidHeaderBody(hb: HeaderBody)
        reads (reveal ReprAAD(); ReprAAD(hb.aad))
        reads ReprEncryptedDataKeys(hb.encryptedDataKeys)
    {
        && ValidAlgorithmID(hb.algorithmSuiteID)
        && ValidMessageId(hb.messageID)
        && ValidAAD(hb.aad)
        && ValidEncryptedDataKeys(hb.encryptedDataKeys)
        && ValidIVLength(hb.ivLength, hb.algorithmSuiteID)
        && ValidFrameLength(hb.frameLength, hb.contentType)
    }

    // TODO: strengthen spec when available
    predicate uniquelyIdentifiesMessage(id: T_MessageID)      { true }
    predicate weaklyBindsHeaderToHeaderBody(id: T_MessageID)  { true }
    predicate enablesSecureReuse(id: T_MessageID)             { true }
    predicate protectsAgainstAccidentalReuse(id: T_MessageID) { true }
    predicate protectsAgainstWearingOut(id: T_MessageID)      { true }
    predicate ValidMessageId(id: T_MessageID) {
        && uniquelyIdentifiesMessage(id)
        && weaklyBindsHeaderToHeaderBody(id)
        && enablesSecureReuse(id)
        && protectsAgainstAccidentalReuse(id)
        && protectsAgainstWearingOut(id)
    }
    predicate ValidAlgorithmID(algorithmSuiteID: AlgorithmSuite.ID) {
        algorithmSuiteID in AlgorithmSuite.Suite.Keys
    }

    function ReprAADUpTo(kvPairs: EncCtx, j: nat): set<object>
        requires j <= kvPairs.Length
        reads kvPairs
    {
        (set i | 0 <= i < j :: kvPairs[i].0) +
        (set i | 0 <= i < j :: kvPairs[i].1)
    }

    function {:opaque} ReprAAD(aad: T_AAD): set<object>
        reads if aad.AAD? then {aad.kvPairs} else {}
    {
        match aad {
            // Not extracting the fields of AAD here for now, but using `aad.` due to https://github.com/dafny-lang/dafny/issues/314
            case AAD(_) =>
                ReprAADUpTo(aad.kvPairs, aad.kvPairs.Length) +
                {aad.kvPairs}
            case EmptyAAD() => {}
        }
    }

    predicate InBoundsKVPairsUpTo(kvPairs: EncCtx, j: nat)
        requires j <= kvPairs.Length
        reads kvPairs
    {
        forall i :: 0 <= i < j ==> 
            && kvPairs[i].0.Length <= UINT16_MAX 
            && kvPairs[i].1.Length <= UINT16_MAX
    }

    predicate InBoundsKVPairs(kvPairs: EncCtx)
        reads kvPairs
    {
        && kvPairs.Length <= UINT16_MAX
        && InBoundsKVPairsUpTo(kvPairs, kvPairs.Length)
    }

    predicate ValidKVPairs(kvPairs: EncCtx)
        reads kvPairs
        reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].0
        reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].1
    {
        forall i :: 0 <= i < kvPairs.Length ==> ValidUTF8(kvPairs[i].0) && ValidUTF8(kvPairs[i].1)
    }

    predicate {:opaque} ValidAAD(aad: T_AAD)
        reads (reveal ReprAAD(); ReprAAD(aad))
    {
        match aad {
            case AAD(kvPairs) =>
                && 0 < kvPairs.Length
                && InBoundsKVPairs(kvPairs)
                && ValidKVPairs(kvPairs)
                && SortedKVPairs(kvPairs)
            case EmptyAAD() => true
        }
    }
    
    function ReprEncryptedDataKeysUpTo(entries: seq<EDKEntry>, j: nat): set<object>
        requires j <= |entries|
    {
        (set i | 0 <= i < j :: entries[i].keyProviderId) +
        (set i | 0 <= i < j :: entries[i].keyProviderInfo) +
        (set i | 0 <= i < j :: entries[i].encDataKey)
    }
    
    function ReprEncryptedDataKeys(encryptedDataKeys: T_EncryptedDataKeys): set<object>
        reads encryptedDataKeys.entries
    {
        ReprEncryptedDataKeysUpTo(encryptedDataKeys.entries[..], encryptedDataKeys.entries.Length) +
        {encryptedDataKeys.entries}
    }

    predicate InBoundsEncryptedDataKeysUpTo(entries: array<EDKEntry>, j: nat)
        requires j <= entries.Length
        reads entries
        reads ReprEncryptedDataKeysUpTo(entries[..], entries.Length)
    {
        forall i :: 0 <= i < j ==>
            && entries[i].keyProviderId.Length   <= UINT16_MAX
            && entries[i].keyProviderInfo.Length <= UINT16_MAX
            && entries[i].encDataKey.Length      <= UINT16_MAX
    }

    predicate InBoundsEncryptedDataKeys(encryptedDataKeys: T_EncryptedDataKeys) 
        reads ReprEncryptedDataKeys(encryptedDataKeys)
    {
        InBoundsEncryptedDataKeysUpTo(encryptedDataKeys.entries, encryptedDataKeys.entries.Length)
    }

    predicate {:opaque} ValidEncryptedDataKeys(encryptedDataKeys: T_EncryptedDataKeys)
        reads ReprEncryptedDataKeys(encryptedDataKeys)
    {
        && InBoundsEncryptedDataKeys(encryptedDataKeys)
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
    predicate ValidIVLength(ivLength: uint8, algorithmSuiteID: AlgorithmSuite.ID)
    {
        algorithmSuiteID in AlgorithmSuite.Suite.Keys && AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen == ivLength
    }
    predicate ValidFrameLength(frameLength: uint32, contentType: T_ContentType)
    {
        match contentType {
            case NonFramed => frameLength == 0
            case Framed => true
        }
    }

    /*
     * Validity of the message header authentication
     */
    predicate ValidAuthenticationTag(authenticationTag: array<uint8>, tagLength: nat, iv: array<uint8>)
    {
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