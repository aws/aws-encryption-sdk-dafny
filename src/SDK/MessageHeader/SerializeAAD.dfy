include "Definitions.dfy"
include "Validity.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.SerializeAAD {
    import opened Definitions
    import opened Validity
    
    import opened Streams
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt

    function encCtxToSeq(kvPairs: EncCtx, i: nat): seq<uint8>
        requires forall i :: 0 <= i < kvPairs.Length ==> kvPairs[i].0.Length <= UINT16_MAX && kvPairs[i].1.Length <= UINT16_MAX
        decreases kvPairs.Length - i
        reads kvPairs
        reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].0
        reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].1
        // reads ReprAADUpTo(kvPairs, kvPairs.Length)
    {
        if i < kvPairs.Length
        then 
            uint16ToSeq(kvPairs[i].0.Length as uint16) + kvPairs[i].0[..] +
            uint16ToSeq(kvPairs[i].1.Length as uint16) + kvPairs[i].1[..] +
            encCtxToSeq(kvPairs, i + 1)
        else []
    }

    function serializeAAD(aad: T_AAD): seq<uint8>
        requires ValidAAD(aad)
        reads ReprAAD(aad)
    {
        match aad {
            case AAD(length, kvPairs) =>
                uint16ToSeq(length) +
                // It would be nicer if this could be a flatten + map as for AAD
                uint16ToSeq(kvPairs.Length as uint16) + encCtxToSeq(kvPairs, 0)
            case EmptyAAD() =>
                uint16ToSeq(0)
        }
    }
    
    method serializeAADImpl(os: StringWriter, aad: T_AAD) returns (ret: Result<nat>)
        requires os.Valid()
        modifies os`data // do we need to establish non-aliasing with encryptedDataKeys here?
        ensures os.Valid()
        requires ValidAAD(aad)
        requires os.Repr !! ReprAAD(aad)
        ensures ValidAAD(aad)
        ensures unchanged(os`Repr)
        ensures unchanged(ReprAAD(aad))
        //ensures old(|os.data|) <= |os.data|
        ensures
            match ret
                case Left(totalWritten) =>
                    var serAAD := serializeAAD(aad);
                    var initLen := old(|os.data|);
                    && totalWritten == |serAAD|
                    && initLen+totalWritten == |os.data|
                    && os.data == old(os.data + serAAD)
                case Right(e) => true
    {
        var totalWritten := 0;
        ghost var initLen := |os.data|;
        ghost var written: seq<nat> := [initLen];
        ghost var i := 0;

        match aad {
            case AAD(length, kvPairs) => {
                {
                    // Key Value Pairs Length (number of bytes of total AAD)
                    var bytes := uint16ToArray(length);
                    ret := os.WriteSimple(bytes);
                    match ret {
                        case Left(len) => totalWritten := totalWritten + len;
                        case Right(e)  => return ret;
                    }
                    i := i + 1;
                    written := written + [initLen + totalWritten];
                    assert written[i] - written[i-1] == bytes.Length;
                    assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    assert totalWritten <= |serializeAAD(aad)|;
                }

                assert 0 < length;
                assert 0 < kvPairs.Length;
                {
                    assert InBoundsKVPairs(kvPairs) ==> kvPairs.Length <= UINT16_MAX;
                    // Key Value Pair Count (number of key value pairs)
                    var bytes := uint16ToArray(kvPairs.Length as uint16);
                    ret := os.WriteSimple(bytes);
                    match ret {
                        case Left(len) => totalWritten := totalWritten + len;
                        case Right(e)  => return ret;
                    }
                    i := i + 1;
                    written := written + [initLen + totalWritten];
                    assert written[i] - written[i-1] == bytes.Length;
                    assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    assert totalWritten <= |serializeAAD(aad)|;
                }
            
                assume false; // TODO: verification times out after this point. I believe that we just do too many heap updates.

                var j := 0;
                while j < kvPairs.Length
                    invariant j <= kvPairs.Length
                    invariant os.Repr !! ReprAAD(aad)
                    invariant unchanged(os`Repr)
                    invariant InBoundsKVPairsUpTo(kvPairs, j)
                    invariant ValidAAD(aad)
                    invariant totalWritten <= |serializeAAD(aad)|
                    invariant initLen+totalWritten <= |os.data|
                    invariant serializeAAD(aad)[written[i-1]-initLen..written[i]-initLen] == os.data[written[i-1]..written[i]];
                    //invariant serializeAAD(aad)[..totalWritten] == os.data[initLen..written[i]];
                {
                    {
                        assert InBoundsKVPairsUpTo(kvPairs, j) ==> kvPairs[j].0.Length <= UINT16_MAX;
                        var bytes := uint16ToArray(kvPairs[j].0.Length as uint16);
                        ret := os.WriteSimple(bytes);
                        match ret {
                            case Left(len) => totalWritten := totalWritten + len;
                            case Right(e)  => return ret;
                        }
                        i := i + 1;
                        written := written + [initLen + totalWritten];
                        assert written[i] - written[i-1] == bytes.Length;
                        assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    }

                    {
                        var bytes := kvPairs[j].0;
                        ret := os.WriteSimple(bytes);
                        match ret {
                            case Left(len) => totalWritten := totalWritten + len;
                            case Right(e)  => return ret;
                        }
                        i := i + 1;
                        written := written + [initLen + totalWritten];
                        assert written[i] - written[i-1] == bytes.Length;
                        assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    }
                    
                    {
                        assert InBoundsKVPairsUpTo(kvPairs, j) ==> kvPairs[j].1.Length <= UINT16_MAX;
                        var bytes := uint16ToArray(kvPairs[j].1.Length as uint16);
                        ret := os.WriteSimple(bytes);
                        match ret {
                            case Left(len) => totalWritten := totalWritten + len;
                            case Right(e)  => return ret;
                        }
                        i := i + 1;
                        written := written + [initLen + totalWritten];
                        assert written[i] - written[i-1] == bytes.Length;
                        assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    }
                    
                    {
                        var bytes := kvPairs[j].1;
                        ret := os.WriteSimple(bytes);
                        match ret {
                            case Left(len) => totalWritten := totalWritten + len;
                            case Right(e)  => return ret;
                        }
                        i := i + 1;
                        written := written + [initLen + totalWritten];
                        assert written[i] - written[i-1] == bytes.Length;
                        assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
                    }
                    j := j + 1;
                }
            }
            case EmptyAAD() => {
                var bytes := uint16ToArray(0);
                ret := os.WriteSimple(bytes);
                match ret {
                    case Left(len) => totalWritten := totalWritten + len;
                    case Right(e)  => return ret;
                }
                i := i + 1;
                written := written + [initLen + totalWritten];
                assert written[i] - written[i-1] == 2;
                assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];

            }
        }
    }
}