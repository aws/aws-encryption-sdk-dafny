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

  // ----- Specification -----

  function SerializeAAD(kvPairs: Materials.EncryptionContext): seq<uint8>
    requires ValidAAD(kvPairs)
  {
    reveal ValidAAD();
    UInt16ToSeq(AADLength(kvPairs) as uint16) +
    var n := |kvPairs|;
    if n == 0 then [] else
      UInt16ToSeq(n as uint16) +
      SerializeKVPairs(kvPairs, 0, n)
  }

  function SerializeKVPairs(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else SerializeKVPairs(kvPairs, lo, hi - 1) + SerializeKVPair(kvPairs[hi - 1])
  }

  function SerializeKVPair(kvPair: (seq<uint8>, seq<uint8>)): seq<uint8>
    requires ValidKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  // Function AADLength is defined without referring to SerializeAAD (because then
  // these two would be mutually recursive with ValidAAD). The following lemma proves
  // that the two definitions correspond.
  lemma ADDLengthCorrect(kvPairs: Materials.EncryptionContext)
    requires ValidAAD(kvPairs)
    ensures |SerializeAAD(kvPairs)| == 2 + AADLength(kvPairs)
  {
    reveal ValidAAD();
    KVPairsLengthCorrect(kvPairs, 0, |kvPairs|);
    /**** Here's a more detailed proof:
    var n := |kvPairs|;
    if n != 0 {
      var s := SerializeKVPairs(kvPairs, 0, n);
      calc {
        |SerializeAAD(kvPairs)|;
      ==  // def. SerializeAAD
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
    ensures |SerializeKVPairs(kvPairs, lo, hi)| == KVPairsLength(kvPairs, lo, hi)
  {
    /**** Here's a more detailed proof:
    if lo < hi {
      var kvPair := kvPairs[hi - 1];
      calc {
        |SerializeKVPairs(kvPairs, lo, hi)|;
      ==  // def. SerializeKVPairs
        |SerializeKVPairs(kvPairs, lo, hi - 1) + SerializeKVPair(kvPair)|;
      ==
        |SerializeKVPairs(kvPairs, lo, hi - 1)| + |SerializeKVPair(kvPair)|;
      ==  { KVPairsLengthCorrect(kvPairs, lo, hi - 1); }
        KVPairsLength(kvPairs, lo, hi - 1) + |SerializeKVPair(kvPair)|;
      ==  // def. SerializeKVPair
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

  // ----- Implementation -----

  method SerializeAADImpl(os: Streams.StringWriter, kvPairs: Materials.EncryptionContext) returns (ret: Result<nat>)
    requires os.Valid() && ValidAAD(kvPairs)
    modifies os`data
    ensures os.Valid() && ValidAAD(kvPairs)
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := SerializeAAD(kvPairs);
        var initLen := old(|os.data|);
        && totalWritten == |serAAD|
        && initLen + totalWritten == |os.data|
        && os.data == old(os.data) + serAAD
      case Failure(e) => true
  {
    reveal ValidAAD();
    var totalWritten := 0;

    // Key Value Pairs Length (number of bytes of total AAD)
    var length :- ComputeAADLength(kvPairs);
    var bytes := UInt16ToSeq(length);
    var len :- os.WriteSimpleSeq(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 2;
    if length == 0 {
      return Success(totalWritten);
    }

    bytes := UInt16ToSeq(|kvPairs| as uint16);
    len :- os.WriteSimpleSeq(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 4;

    var j := 0;
    ghost var n := |kvPairs|;
    while j < |kvPairs|
      invariant j <= n == |kvPairs|
      invariant os.data ==
        old(os.data) +
        UInt16ToSeq(length) +
        UInt16ToSeq(n as uint16) +
        SerializeKVPairs(kvPairs, 0, j)
      invariant totalWritten == 4 + |SerializeKVPairs(kvPairs, 0, j)|
    {
      bytes := UInt16ToSeq(|kvPairs[j].0| as uint16);
      len :- os.WriteSimpleSeq(bytes);
      totalWritten := totalWritten + len;

      len :- os.WriteSimpleSeq(kvPairs[j].0);
      totalWritten := totalWritten + len;

      bytes := UInt16ToSeq(|kvPairs[j].1| as uint16);
      len :- os.WriteSimpleSeq(bytes);
      totalWritten := totalWritten + len;

      len :- os.WriteSimpleSeq(kvPairs[j].1);
      totalWritten := totalWritten + len;

      j := j + 1;
    }
    
    return Success(totalWritten);
  }

  method ComputeAADLength(kvPairs: Materials.EncryptionContext) returns (res: Result<uint16>)
    requires |kvPairs| < UINT16_LIMIT
    requires forall i :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    ensures match res
      case Success(len) => len as int == AADLength(kvPairs)
      case Failure(_) => UINT16_LIMIT <= AADLength(kvPairs)
  {
    var n: int32 := |kvPairs| as int32;
    if n == 0 {
      return Success(0);
    } else {
      var len: int32, limit: int32 := 2, UINT16_LIMIT as int32;
      var i: int32 := 0;
      while i < n
        invariant i <= n
        invariant 2 + KVPairsLength(kvPairs, 0, i as int) == len as int < UINT16_LIMIT
      {
        var kvPair := kvPairs[i];
        len := len + 4 + |kvPair.0| as int32 + |kvPair.1| as int32;
        KVPairsLengthSplit(kvPairs, 0, i as int + 1, n as int);
        if limit <= len {
          return Failure("The number of bytes in encryption context exceeds the allowed maximum");
        }
        i := i + 1;
      }
      return Success(len as uint16);
    }
  }
}
