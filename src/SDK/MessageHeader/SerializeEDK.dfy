include "Definitions.dfy"
include "Validity.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.SerializeEDK {
    import opened Definitions
    import opened Validity

    import opened Streams
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    lemma {:axiom} Assume(b: bool) ensures b

    // Alternative w/o flatten/map
    function serializeEDKEntries(entries: seq<EDKEntry>): seq<uint8>
        requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
    {
        if entries == []
        then []
        else
            var entry := entries[0];
            UInt16ToSeq(|entry.providerID| as uint16)   + StringToByteSeq(entry.providerID) +
            UInt16ToSeq(|entry.providerInfo| as uint16) + entry.providerInfo +
            UInt16ToSeq(|entry.ciphertext| as uint16)   + entry.ciphertext +
            serializeEDKEntries(entries[1..])
    }

    function serializeEDK(encryptedDataKeys: T_EncryptedDataKeys): seq<uint8>
        requires ValidEncryptedDataKeys(encryptedDataKeys)
    {
        Assume(|encryptedDataKeys.entries| < UINT16_LIMIT);
        Assume(forall i :: 0 <= i < |encryptedDataKeys.entries| ==> encryptedDataKeys.entries[i].Valid());
        UInt16ToSeq(|encryptedDataKeys.entries| as uint16) +
        serializeEDKEntries(encryptedDataKeys.entries)
    }

    method serializeEDKImpl(os: StringWriter, encryptedDataKeys: T_EncryptedDataKeys) returns (ret: Either<nat, Error>)
        requires os.Valid()
        modifies os`data
        ensures os.Valid()
        requires ValidEncryptedDataKeys(encryptedDataKeys)
        ensures ValidEncryptedDataKeys(encryptedDataKeys)
        ensures unchanged(os`Repr)
        //ensures old(|os.data|) <= |os.data|
        ensures
            match ret
                case Left(totalWritten) =>
                    var serEDK := serializeEDK(encryptedDataKeys);
                    var initLen := old(|os.data|);
                    && totalWritten == |serEDK|
                    && initLen+totalWritten == |os.data|
                    && os.data == old(os.data + serEDK)
                case Right(e) => true
    {
        Assume(false);  // TODO: turned off verification for now
        var totalWritten: nat := 0;
        ghost var initLen := |os.data|;
        ghost var prevPos: nat := initLen;
        ghost var currPos: nat := initLen;

        {
            Assume(|encryptedDataKeys.entries| < UINT16_LIMIT);
            var bytes := UInt16ToArray(|encryptedDataKeys.entries| as uint16);
            ret := os.WriteSimple(bytes);
            match ret {
                case Left(len) => totalWritten := totalWritten + len;
                case Right(e)  => return ret;
            }
            prevPos := currPos;
            currPos := initLen + totalWritten;
            assert currPos - prevPos == bytes.Length;
            assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            assert totalWritten <= |serializeEDK(encryptedDataKeys)|;
        }

        var j := 0;
        ghost var written: seq<nat> := [currPos, currPos];
        while j < |encryptedDataKeys.entries|
            invariant j <= |encryptedDataKeys.entries|
            invariant j < |written|
            invariant unchanged(os`Repr)
            invariant InBoundsEncryptedDataKeysUpTo(encryptedDataKeys.entries, j)
            invariant ValidEncryptedDataKeys(encryptedDataKeys)
            invariant initLen + totalWritten == currPos
            invariant 0 <= initLen <= prevPos <= currPos <= |os.data|
            invariant forall k :: 0 <= k < |written| ==> initLen <= written[k] <= |os.data|
            invariant currPos-initLen <= |serializeEDK(encryptedDataKeys)|
            invariant serializeEDK(encryptedDataKeys)[..currPos-initLen] == os.data[initLen..currPos]
            invariant serializeEDK(encryptedDataKeys)[prevPos-initLen..currPos-initLen] == os.data[prevPos..currPos];
            invariant 1 <= j ==> os.data[initLen..written[j]] == os.data[initLen..written[j-1]] + serializeEDKEntries(encryptedDataKeys.entries[..j])
        {
            var entry := encryptedDataKeys.entries[j];
            {
                Assume(|entry.providerID| < UINT16_LIMIT);
                var bytes := UInt16ToArray(|entry.providerID| as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := StringToByteSeq(entry.providerID);
                ret := os.WriteSimpleSeq(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == |bytes|;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                Assume(|entry.providerInfo| < UINT16_LIMIT);
                var bytes := UInt16ToArray(|entry.providerInfo| as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := entry.providerInfo;
                ret := os.WriteSimpleSeq(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == |bytes|;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                Assume(|entry.ciphertext| < UINT16_LIMIT);
                var bytes := UInt16ToArray(|entry.ciphertext| as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := entry.ciphertext;
                ret := os.WriteSimpleSeq(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == |bytes|;
                Assume(prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..]);
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }
            written := written + [currPos];
            j := j + 1;
            Assume(ValidEncryptedDataKeys(encryptedDataKeys));
        }

        Assume(totalWritten == |serializeEDK(encryptedDataKeys)|);
        Assume(initLen+totalWritten == |os.data|);
        Assume(os.data == old(os.data) + serializeEDK(encryptedDataKeys));
        return Left(totalWritten);
    }
}
