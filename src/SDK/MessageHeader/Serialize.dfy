include "Format.dfy"
include "../AlgorithmSuite.dfy"

include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module MessageHeader.Serialize {
  import Msg = Definitions
  import SerializeAAD
  import SerializeEDK
  import V = Validity
  import AlgorithmSuite

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  function {:opaque} Serialize(hb: Msg.HeaderBody): seq<uint8>
    requires V.ValidHeaderBody(hb)
  {
    reveal V.ValidHeaderBody();
    [hb.version as uint8] +
    [hb.typ as uint8] +
    UInt16ToSeq(hb.algorithmSuiteID as uint16) +
    hb.messageID +
    SerializeAAD.SerializeAAD(hb.aad) +
    SerializeEDK.SerializeEDKs(hb.encryptedDataKeys) +
    [Msg.ContentTypeToUInt8(hb.contentType)] +
    hb.reserved +
    [hb.ivLength] +
    UInt32ToSeq(hb.frameLength)
  }

  method SerializeHeaderBody(wr: Streams.StringWriter, hb: Msg.HeaderBody) returns (ret: Result<nat>)
    requires wr.Valid() && V.ValidHeaderBody(hb)
    modifies wr`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHb := (reveal Serialize(); Serialize(hb));
        var initLen := old(|wr.data|);
        && totalWritten == |serHb|
        && initLen + totalWritten == |wr.data|
        && serHb == wr.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var totalWritten := 0;

    var len :- wr.WriteSingleByteSimple(hb.version as uint8);
    totalWritten := totalWritten + len;

    len :- wr.WriteSingleByteSimple(hb.typ as uint8);
    totalWritten := totalWritten + len;

    var bytes := UInt16ToArray(hb.algorithmSuiteID as uint16);
    len :- wr.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    len :- wr.WriteSimpleSeq(hb.messageID);
    totalWritten := totalWritten + len;

    reveal V.ValidHeaderBody();
    len :- SerializeAAD.SerializeAADImpl(wr, hb.aad);
    totalWritten := totalWritten + len;

    len :- SerializeEDK.SerializeEDKsImpl(wr, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;

    var contentType := Msg.ContentTypeToUInt8(hb.contentType);
    len :- wr.WriteSingleByteSimple(contentType);
    totalWritten := totalWritten + len;

    len :- wr.WriteSimpleSeq(hb.reserved);
    totalWritten := totalWritten + len;

    len :- wr.WriteSingleByteSimple(hb.ivLength);
    totalWritten := totalWritten + len;

    bytes := UInt32ToArray(hb.frameLength);
    len :- wr.WriteSimple(bytes);
    totalWritten := totalWritten + len;

    reveal Serialize();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(wr: Streams.StringWriter, ha: Msg.HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<nat>)
    requires wr.Valid()
    requires V.ValidHeaderAuthentication(ha, algorithmSuiteID)
    modifies wr`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHa := ha.iv + ha.authenticationTag;
        var initLen := old(|wr.data|);
        && totalWritten == |serHa|
        && initLen + totalWritten == |wr.data|
        && serHa == wr.data[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var m :- wr.WriteSimpleSeq(ha.iv);
    var n :- wr.WriteSimpleSeq(ha.authenticationTag);
    return Success(m + n);
  }
}


module MessageHeader.SerializeAAD {
  import V = Validity
  import Materials

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // ----- Specification -----

  function SerializeAAD(kvPairs: Materials.EncryptionContext): seq<uint8>
    requires V.ValidAAD(kvPairs)
  {
    reveal V.ValidAAD();
    UInt16ToSeq(V.AADLength(kvPairs) as uint16) +
    var n := |kvPairs|;
    if n == 0 then [] else
      UInt16ToSeq(n as uint16) +
      SerializeKVPairs(kvPairs, 0, n)
  }

  function SerializeKVPairs(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |kvPairs| ==> V.ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
  {
    if lo == hi then [] else SerializeKVPairs(kvPairs, lo, hi - 1) + SerializeKVPair(kvPairs[hi - 1])
  }

  function SerializeKVPair(kvPair: (seq<uint8>, seq<uint8>)): seq<uint8>
    requires V.ValidKVPair(kvPair)
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 +
    UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  // Function V.AADLength is defined without referring to SerializeAAD (because then
  // these two would be mutually recursive with V.ValidAAD). The following lemma proves
  // that the two definitions correspond.
  lemma ADDLengthCorrect(kvPairs: Materials.EncryptionContext)
    requires V.ValidAAD(kvPairs)
    ensures |SerializeAAD(kvPairs)| == 2 + V.AADLength(kvPairs)
  {
    reveal V.ValidAAD();
    KVPairsLengthCorrect(kvPairs, 0, |kvPairs|);
    /**** Here's a more detailed proof:
    var n := |kvPairs|;
    if n != 0 {
      var s := SerializeKVPairs(kvPairs, 0, n);
      calc {
        |SerializeAAD(kvPairs)|;
      ==  // def. SerializeAAD
        |UInt16ToSeq(V.AADLength(kvPairs) as uint16) + UInt16ToSeq(n as uint16) + s|;
      ==  // UInt16ToSeq yields length-2 sequence
        2 + 2 + |s|;
      ==  { KVPairsLengthCorrect(kvPairs, 0, n); }
        2 + 2 + V.KVPairsLength(kvPairs, 0, n);
      }
    }
    ****/
  }

  lemma KVPairsLengthCorrect(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat)
    requires forall i :: 0 <= i < |kvPairs| ==> V.ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
    ensures |SerializeKVPairs(kvPairs, lo, hi)| == V.KVPairsLength(kvPairs, lo, hi)
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
        V.KVPairsLength(kvPairs, lo, hi - 1) + |SerializeKVPair(kvPair)|;
      ==  // def. SerializeKVPair
        V.KVPairsLength(kvPairs, lo, hi - 1) +
        |UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1|;
      ==
        V.KVPairsLength(kvPairs, lo, hi - 1) + 2 + |kvPair.0| + 2 + |kvPair.1|;
      ==  // def. V.KVPairsLength
        V.KVPairsLength(kvPairs, lo, hi);
      }
    }
    ****/
  }

  // ----- Implementation -----

  method SerializeAADImpl(wr: Streams.StringWriter, kvPairs: Materials.EncryptionContext) returns (ret: Result<nat>)
    requires wr.Valid() && V.ValidAAD(kvPairs)
    modifies wr`data
    ensures wr.Valid() && V.ValidAAD(kvPairs)
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := SerializeAAD(kvPairs);
        var initLen := old(|wr.data|);
        && totalWritten == |serAAD|
        && initLen + totalWritten == |wr.data|
        && wr.data == old(wr.data) + serAAD
      case Failure(e) => true
  {
    reveal V.ValidAAD();
    var totalWritten := 0;

    // Key Value Pairs Length (number of bytes of total AAD)
    var length :- ComputeAADLength(kvPairs);
    var bytes := UInt16ToSeq(length);
    var len :- wr.WriteSimpleSeq(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 2;
    if length == 0 {
      return Success(totalWritten);
    }

    bytes := UInt16ToSeq(|kvPairs| as uint16);
    len :- wr.WriteSimpleSeq(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 4;

    var j := 0;
    ghost var n := |kvPairs|;
    while j < |kvPairs|
      invariant j <= n == |kvPairs|
      invariant wr.data ==
        old(wr.data) +
        UInt16ToSeq(length) +
        UInt16ToSeq(n as uint16) +
        SerializeKVPairs(kvPairs, 0, j)
      invariant totalWritten == 4 + |SerializeKVPairs(kvPairs, 0, j)|
    {
      bytes := UInt16ToSeq(|kvPairs[j].0| as uint16);
      len :- wr.WriteSimpleSeq(bytes);
      totalWritten := totalWritten + len;

      len :- wr.WriteSimpleSeq(kvPairs[j].0);
      totalWritten := totalWritten + len;

      bytes := UInt16ToSeq(|kvPairs[j].1| as uint16);
      len :- wr.WriteSimpleSeq(bytes);
      totalWritten := totalWritten + len;

      len :- wr.WriteSimpleSeq(kvPairs[j].1);
      totalWritten := totalWritten + len;

      j := j + 1;
    }
    
    return Success(totalWritten);
  }

  method ComputeAADLength(kvPairs: Materials.EncryptionContext) returns (res: Result<uint16>)
    requires |kvPairs| < UINT16_LIMIT
    requires forall i :: 0 <= i < |kvPairs| ==> V.ValidKVPair(kvPairs[i])
    ensures match res
      case Success(len) => len as int == V.AADLength(kvPairs)
      case Failure(_) => UINT16_LIMIT <= V.AADLength(kvPairs)
  {
    var n: int32 := |kvPairs| as int32;
    if n == 0 {
      return Success(0);
    } else {
      var len: int32, limit: int32 := 2, UINT16_LIMIT as int32;
      var i: int32 := 0;
      while i < n
        invariant i <= n
        invariant 2 + V.KVPairsLength(kvPairs, 0, i as int) == len as int < UINT16_LIMIT
      {
        var kvPair := kvPairs[i];
        len := len + 4 + |kvPair.0| as int32 + |kvPair.1| as int32;
        V.KVPairsLengthSplit(kvPairs, 0, i as int + 1, n as int);
        if limit <= len {
          return Failure("The number of bytes in encryption context exceeds the allowed maximum");
        }
        i := i + 1;
      }
      return Success(len as uint16);
    }
  }
}


module MessageHeader.SerializeEDK {
  import Msg = Definitions
  import V = Validity
  import Materials

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // ----- Specification -----

  function SerializeEDKs(encryptedDataKeys: Msg.EncryptedDataKeys): seq<uint8>
    requires V.ValidEncryptedDataKeys(encryptedDataKeys)
  {
    reveal V.ValidEncryptedDataKeys();
    var n := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) +
    SerializeEDKEntries(encryptedDataKeys.entries, 0, n)
  }

  function SerializeEDKEntries(entries: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
  {
    if lo == hi then [] else SerializeEDKEntries(entries, lo, hi - 1) + SerializeEDKEntry(entries[hi - 1])
  }

  function SerializeEDKEntry(edk: Materials.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
  {
    UInt16ToSeq(|edk.providerID| as uint16)   + StringToByteSeq(edk.providerID) +
    UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo +
    UInt16ToSeq(|edk.ciphertext| as uint16)   + edk.ciphertext
  }

  // ----- Implementation -----

  method SerializeEDKsImpl(wr: Streams.StringWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: Result<nat>)
    requires wr.Valid() && V.ValidEncryptedDataKeys(encryptedDataKeys)
    modifies wr`data
    ensures wr.Valid() && V.ValidEncryptedDataKeys(encryptedDataKeys)
    ensures match ret
      case Success(totalWritten) =>
        var serEDK := SerializeEDKs(encryptedDataKeys);
        var initLen := old(|wr.data|);
        && totalWritten == |serEDK|
        && initLen + totalWritten == |wr.data|
        && wr.data == old(wr.data) + serEDK
      case Failure(e) => true
  {
    reveal V.ValidEncryptedDataKeys();

    var totalWritten := 0;

    var bytes := UInt16ToArray(|encryptedDataKeys.entries| as uint16);
    var len :- wr.WriteSimple(bytes);
    totalWritten := totalWritten + len;
    assert totalWritten == 2;

    var j := 0;
    ghost var n := |encryptedDataKeys.entries|;
    while j < |encryptedDataKeys.entries|
      invariant j <= n == |encryptedDataKeys.entries|
      invariant wr.data ==
        old(wr.data) +
        UInt16ToSeq(n as uint16) +
        SerializeEDKEntries(encryptedDataKeys.entries, 0, j);
      invariant totalWritten == 2 + |SerializeEDKEntries(encryptedDataKeys.entries, 0, j)|
    {
      var entry := encryptedDataKeys.entries[j];

      bytes := UInt16ToArray(|entry.providerID| as uint16);
      len :- wr.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      var byteSeq := StringToByteSeq(entry.providerID);
      len :- wr.WriteSimpleSeq(byteSeq);
      totalWritten := totalWritten + len;

      bytes := UInt16ToArray(|entry.providerInfo| as uint16);
      len :- wr.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      len :- wr.WriteSimpleSeq(entry.providerInfo);
      totalWritten := totalWritten + len;

      bytes := UInt16ToArray(|entry.ciphertext| as uint16);
      len :- wr.WriteSimple(bytes);
      totalWritten := totalWritten + len;

      len :- wr.WriteSimpleSeq(entry.ciphertext);
      totalWritten := totalWritten + len;

      j := j + 1;
    }

    return Success(totalWritten);
  }
}
