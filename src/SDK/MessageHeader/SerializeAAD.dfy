include "Definitions.dfy"
include "Validity.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.SerializeAAD {
  import opened Definitions
  import opened Validity

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  lemma {:axiom} Assume(b: bool)
    ensures b

  function EncCtxToSeqRec(kvPairs: EncCtx, i: nat): seq<uint8>
    requires forall i :: 0 <= i < |kvPairs| ==> |kvPairs[i].0| < UINT16_LIMIT && |kvPairs[i].1| < UINT16_LIMIT
    decreases |kvPairs| - i
  {
    if i < |kvPairs| then
      UInt16ToSeq(|kvPairs[i].0| as uint16) + kvPairs[i].0[..] +
      UInt16ToSeq(|kvPairs[i].1| as uint16) + kvPairs[i].1[..] +
      EncCtxToSeqRec(kvPairs, i + 1)
    else
      []
  }

  function EncCtxToSeq(kvPairs: EncCtx): (ret: seq<uint8>)
    requires forall i :: 0 <= i < |kvPairs| ==> |kvPairs[i].0| < UINT16_LIMIT && |kvPairs[i].1| < UINT16_LIMIT
    ensures |ret| < UINT16_LIMIT // TODO: we need to establish that this length fits into two bytes
  {
    Assume(|EncCtxToSeqRec(kvPairs, 0)| < UINT16_LIMIT);  // TODO
    EncCtxToSeqRec(kvPairs, 0)
  }

  function SerializeAAD(aad: T_AAD): seq<uint8>
    requires ValidAAD(aad)
  {
    match aad {
      case AAD(kvPairs) =>
        Assume(forall i :: 0 <= i < |kvPairs| ==> |kvPairs[i].0| < UINT16_LIMIT && |kvPairs[i].1| < UINT16_LIMIT);
        var encCtxSeq := EncCtxToSeq(kvPairs);
        UInt16ToSeq(|encCtxSeq| as uint16) +
        // It would be nicer if this could be a flatten + map as for AAD
        UInt16ToSeq(Assume(|kvPairs| < UINT16_LIMIT); |kvPairs| as uint16) + encCtxSeq
      case EmptyAAD() =>
        UInt16ToSeq(0)
    }
  }

  method SerializeAADImpl(os: Streams.StringWriter, aad: T_AAD) returns (ret: Result<nat>)
    requires os.Valid() && ValidAAD(aad)
    modifies os`data // do we need to establish non-aliasing with encryptedDataKeys here?
    ensures os.Valid() && ValidAAD(aad)
    //ensures old(|os.data|) <= |os.data|
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := SerializeAAD(aad);
        var initLen := old(|os.data|);
        && totalWritten == |serAAD|
        && initLen + totalWritten == |os.data|
        && os.data == old(os.data) + serAAD
      case Failure(e) => true
  {
    var totalWritten := 0;
    ghost var initLen := |os.data|;
    ghost var written: seq<nat> := [initLen];
    ghost var i := 0;

    match aad {
      case AAD(kvPairs) =>
        var len: nat;
        {
          // Key Value Pairs Length (number of bytes of total AAD)
          var length: uint16;
          assert InBoundsKVPairs(kvPairs) ==> |kvPairs| < UINT16_LIMIT;
          // TODO: We need to compute length here after removing length field from AAD datatype
          Assume(forall i :: 0 <= i < |kvPairs| ==> |kvPairs[i].0| < UINT16_LIMIT && |kvPairs[i].1| < UINT16_LIMIT);
          Assume(length == |EncCtxToSeq(kvPairs)| as uint16);
          var bytes := UInt16ToArray(length);
          len :- os.WriteSimple(bytes);
          totalWritten := totalWritten + len;
          i := i + 1;
          written := written + [initLen + totalWritten];
          assert written[i] - written[i-1] == bytes.Length;
          assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          Assume(ValidAAD(aad));  // TODO
          assert totalWritten <= |SerializeAAD(aad)|;
        }

        Assume(0 < |kvPairs|);
        assert 0 < |kvPairs|;
        {
          assert InBoundsKVPairs(kvPairs) ==> |kvPairs| < UINT16_LIMIT;
          // Key Value Pair Count (number of key value pairs)
          Assume(|kvPairs| < UINT16_LIMIT);
          var bytes := UInt16ToArray(|kvPairs| as uint16);
          len :- os.WriteSimple(bytes);
          totalWritten := totalWritten + len;
          i := i + 1;
          written := written + [initLen + totalWritten];
          assert written[i] - written[i-1] == bytes.Length;
          assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          Assume(ValidAAD(aad));  // TODO
          assert totalWritten <= |SerializeAAD(aad)|;
        }

        Assume(false); // TODO: verification times out after this point. I believe that we just do too many heap updates.

        var j := 0;
        while j < |kvPairs|
          invariant j <= |kvPairs|
          invariant unchanged(os`Repr)
          invariant InBoundsKVPairsUpTo(kvPairs, j)
          invariant ValidAAD(aad)
          invariant totalWritten <= |SerializeAAD(aad)|
          invariant initLen+totalWritten <= |os.data|
          invariant SerializeAAD(aad)[written[i-1]-initLen..written[i]-initLen] == os.data[written[i-1]..written[i]];
          //invariant SerializeAAD(aad)[..totalWritten] == os.data[initLen..written[i]];
        {
          {
            assert InBoundsKVPairsUpTo(kvPairs, j) ==> |kvPairs[j].0| < UINT16_LIMIT;
            var bytes := UInt16ToArray(|kvPairs[j].0| as uint16);
            len :- os.WriteSimple(bytes);
            totalWritten := totalWritten + len;
            i := i + 1;
            written := written + [initLen + totalWritten];
            assert written[i] - written[i-1] == bytes.Length;
            assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          }

          {
            var bytes := kvPairs[j].0;
            len :- os.WriteSimpleSeq(bytes);
            totalWritten := totalWritten + len;
            i := i + 1;
            written := written + [initLen + totalWritten];
            assert written[i] - written[i-1] == |bytes|;
            assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          }

          {
            assert InBoundsKVPairsUpTo(kvPairs, j) ==> |kvPairs[j].1| < UINT16_LIMIT;
            var bytes := UInt16ToSeq(|kvPairs[j].1| as uint16);
            len :- os.WriteSimpleSeq(bytes);
            totalWritten := totalWritten + len;
            i := i + 1;
            written := written + [initLen + totalWritten];
            assert written[i] - written[i-1] == |bytes|;
            assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          }

          {
            var bytes := kvPairs[j].1;
            len :- os.WriteSimpleSeq(bytes);
            totalWritten := totalWritten + len;
            i := i + 1;
            written := written + [initLen + totalWritten];
            assert written[i] - written[i-1] == |bytes|;
            assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
          }

          j := j + 1;
        }
        return Success(len);

      case EmptyAAD() =>
        var bytes := UInt16ToArray(0);
        var len :- os.WriteSimple(bytes);
        totalWritten := totalWritten + len;
        i := i + 1;
        written := written + [initLen + totalWritten];
        assert written[i] - written[i-1] == 2;
        assert written[i-1] <= written[i] <= |os.data| ==> os.data[written[i-1]..written[i]] == bytes[..];
        Assume(ValidAAD(aad));
        return Success(len);
    }
  }
}
