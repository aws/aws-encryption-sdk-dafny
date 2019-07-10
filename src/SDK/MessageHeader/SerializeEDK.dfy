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

    // Alternative w/o flatten/map
    function serializeEDKEntries(entries: seq<EDKEntry>): seq<uint8>
        requires forall i :: 0 <= i < |entries| ==>
            && entries[i].keyProviderId.Length   <= UINT16_MAX
            && entries[i].keyProviderInfo.Length <= UINT16_MAX
            && entries[i].encDataKey.Length      <= UINT16_MAX
        reads ReprEncryptedDataKeysUpTo(entries, |entries|)
    {
        if entries == []
        then []
        else
            var entry := entries[0];
            uint16ToSeq(entry.keyProviderId.Length as uint16)   + entry.keyProviderId[..] +
            uint16ToSeq(entry.keyProviderInfo.Length as uint16) + entry.keyProviderInfo[..] +
            uint16ToSeq(entry.encDataKey.Length as uint16)      + entry.encDataKey[..] +
            serializeEDKEntries(entries[1..])
    }

    function serializeEDK(encryptedDataKeys: T_EncryptedDataKeys): seq<uint8>
        requires ValidEncryptedDataKeys(encryptedDataKeys)
        reads ReprEncryptedDataKeys(encryptedDataKeys)
    {
        uint16ToSeq(encryptedDataKeys.count) +
        serializeEDKEntries(encryptedDataKeys.entries[..])
    }

    method serializeEDKImpl(os: StringWriter, encryptedDataKeys: T_EncryptedDataKeys) returns (ret: Result<nat>)
        requires os.Valid()
        modifies os`data
        ensures os.Valid()
        requires ValidEncryptedDataKeys(encryptedDataKeys)
        requires os.Repr !! ReprEncryptedDataKeys(encryptedDataKeys)
        ensures ValidEncryptedDataKeys(encryptedDataKeys)
        ensures unchanged(os`Repr)
        ensures unchanged(ReprEncryptedDataKeys(encryptedDataKeys))
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
        var totalWritten: nat := 0;
        ghost var initLen := |os.data|;
        ghost var prevPos: nat := initLen;
        ghost var currPos: nat := initLen;

        {
            var bytes := uint16ToArray(encryptedDataKeys.count as uint16);
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
        assume false;

        var j := 0;
        ghost var written: seq<nat> := [currPos, currPos];
        while j < encryptedDataKeys.entries.Length
            invariant j <= encryptedDataKeys.entries.Length
            invariant j < |written|
            invariant os.Repr !! ReprEncryptedDataKeys(encryptedDataKeys)
            invariant unchanged(os`Repr)
            invariant InBoundsEncryptedDataKeysUpTo(encryptedDataKeys.entries, j)
            invariant ValidEncryptedDataKeys(encryptedDataKeys)
            invariant initLen + totalWritten == currPos
            invariant 0 <= initLen <= prevPos <= currPos <= |os.data|
            invariant currPos-initLen <= |serializeEDK(encryptedDataKeys)|
            invariant serializeEDK(encryptedDataKeys)[..currPos-initLen] == os.data[initLen..currPos]
            invariant serializeEDK(encryptedDataKeys)[prevPos-initLen..currPos-initLen] == os.data[prevPos..currPos];
            invariant 1 <= j ==> os.data[initLen..written[j]] == os.data[initLen..written[j-1]] + serializeEDKEntries(encryptedDataKeys.entries[..j])
        {
            var entry := encryptedDataKeys.entries[j];
            {
                var bytes := uint16ToArray(entry.keyProviderId.Length as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := entry.keyProviderId;
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := uint16ToArray(entry.keyProviderInfo.Length as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := entry.keyProviderInfo;
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := uint16ToArray(entry.encDataKey.Length as uint16);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }

            {
                var bytes := entry.encDataKey;
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                prevPos := currPos;
                currPos := initLen + totalWritten;
                assert currPos - prevPos == bytes.Length;
                assert prevPos <= currPos <= |os.data| ==> os.data[prevPos..currPos] == bytes[..];
            }
            written := written + [currPos];
            j := j + 1;
        }
    }
}