include "MessageHeader.dfy"
include "Materials.dfy"
include "AlgorithmSuite.dfy"

include "../Util/Streams.dfy"
include "../StandardLibrary/StandardLibrary.dfy"

module Serialize {
  import Msg = MessageHeader
  import AlgorithmSuite

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials

  method SerializeHeaderBody(wr: Streams.ByteWriter, hb: Msg.HeaderBody) returns (ret: Result<nat>)
    requires wr.Valid() && hb.Valid()
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHb := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(hb));
        var initLen := old(wr.GetSizeWritten());
        && totalWritten == |serHb|
        && initLen + totalWritten == wr.GetSizeWritten()
        && serHb == wr.GetDataWritten()[initLen..initLen + totalWritten]
      case Failure(e) => true
  {
    var totalWritten := 0;

    var len := wr.WriteByte(hb.version as uint8);
    totalWritten := totalWritten + len;

    len := wr.WriteByte(hb.typ as uint8);
    totalWritten := totalWritten + len;

    len := wr.WriteUInt16(hb.algorithmSuiteID as uint16);
    totalWritten := totalWritten + len;

    len := wr.WriteBytes(hb.messageID);
    totalWritten := totalWritten + len;

    len :- SerializeAAD(wr, hb.aad);
    totalWritten := totalWritten + len;

    len :- SerializeEDKs(wr, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;

    var contentType := Msg.ContentTypeToUInt8(hb.contentType);
    len := wr.WriteByte(contentType);
    totalWritten := totalWritten + len;

    len := wr.WriteBytes(Msg.Reserved);
    totalWritten := totalWritten + len;

    len := wr.WriteByte(hb.ivLength);
    totalWritten := totalWritten + len;

    len := wr.WriteUInt32(hb.frameLength);
    totalWritten := totalWritten + len;

    reveal Msg.HeaderBodyToSeq();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(wr: Streams.ByteWriter, ha: Msg.HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<nat>)
    requires wr.Valid()
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serHa := ha.iv + ha.authenticationTag;
        var initLen := old(wr.GetSizeWritten());
        && initLen + totalWritten == wr.GetSizeWritten()
        && serHa == wr.GetDataWritten()[initLen..initLen + totalWritten]
        && totalWritten == |serHa|
      case Failure(e) => true
  {
    var m := wr.WriteBytes(ha.iv);
    var n := wr.WriteBytes(ha.authenticationTag);
    return Success(m + n);
  }

  // ----- SerializeAAD -----

  method SerializeAAD(wr: Streams.ByteWriter, kvPairs: Materials.EncryptionContext) returns (ret: Result<nat>)
    requires wr.Valid() && Msg.ValidAAD(kvPairs)
    modifies wr.writer`data
    ensures wr.Valid() && Msg.ValidAAD(kvPairs)
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := Msg.AADToSeq(kvPairs);
        var initLen := old(wr.GetSizeWritten());
        && totalWritten == |serAAD|
        && initLen + totalWritten == wr.GetSizeWritten()
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD
      case Failure(e) => true
  {
    reveal Msg.ValidAAD();
    var totalWritten := 0;

    // Key Value Pairs Length (number of bytes of total AAD)
    var aadLength :- ComputeAADLength(kvPairs);
    var len := wr.WriteUInt16(aadLength);
    totalWritten := totalWritten + len;
    if aadLength == 0 {
      return Success(totalWritten);
    }

    len := wr.WriteUInt16(|kvPairs| as uint16);
    totalWritten := totalWritten + len;

    var j := 0;
    ghost var n := |kvPairs|;
    while j < |kvPairs|
      invariant j <= n == |kvPairs|
      invariant wr.GetDataWritten() ==
        old(wr.GetDataWritten()) +
        UInt16ToSeq(aadLength) +
        UInt16ToSeq(n as uint16) +
        Msg.KVPairsToSeq(kvPairs, 0, j)
      invariant totalWritten == 4 + |Msg.KVPairsToSeq(kvPairs, 0, j)|
    {
      len := wr.WriteUInt16(|kvPairs[j].0| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(kvPairs[j].0);
      totalWritten := totalWritten + len;

      len := wr.WriteUInt16(|kvPairs[j].1| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(kvPairs[j].1);
      totalWritten := totalWritten + len;

      j := j + 1;
    }
    
    return Success(totalWritten);
  }

  method ComputeAADLength(kvPairs: Materials.EncryptionContext) returns (res: Result<uint16>)
    requires |kvPairs| < UINT16_LIMIT
    requires forall i :: 0 <= i < |kvPairs| ==> Msg.ValidKVPair(kvPairs[i])
    ensures match res
      case Success(len) => len as int == Msg.AADLength(kvPairs)
      case Failure(_) => UINT16_LIMIT <= Msg.AADLength(kvPairs)
  {
    var n: int32 := |kvPairs| as int32;
    if n == 0 {
      return Success(0);
    } else {
      var len: int32, limit: int32 := 2, UINT16_LIMIT as int32;
      var i: int32 := 0;
      while i < n
        invariant i <= n
        invariant 2 + Msg.KVPairsLength(kvPairs, 0, i as int) == len as int < UINT16_LIMIT
      {
        var kvPair := kvPairs[i];
        len := len + 4 + |kvPair.0| as int32 + |kvPair.1| as int32;
        Msg.KVPairsLengthSplit(kvPairs, 0, i as int + 1, n as int);
        if limit <= len {
          return Failure("The number of bytes in encryption context exceeds the allowed maximum");
        }
        i := i + 1;
      }
      return Success(len as uint16);
    }
  }

  // ----- SerializeEDKs -----

  method SerializeEDKs(wr: Streams.ByteWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: Result<nat>)
    requires wr.Valid() && encryptedDataKeys.Valid()
    modifies wr.writer`data
    ensures wr.Valid() && encryptedDataKeys.Valid()
    ensures match ret
      case Success(totalWritten) =>
        var serEDK := Msg.EDKsToSeq(encryptedDataKeys);
        var initLen := old(wr.GetSizeWritten());
        && totalWritten == |serEDK|
        && initLen + totalWritten == wr.GetSizeWritten()
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serEDK
      case Failure(e) => true
  {
    var totalWritten := 0;

    var len := wr.WriteUInt16(|encryptedDataKeys.entries| as uint16);
    totalWritten := totalWritten + len;

    var j := 0;
    ghost var n := |encryptedDataKeys.entries|;
    while j < |encryptedDataKeys.entries|
      invariant j <= n == |encryptedDataKeys.entries|
      invariant wr.GetDataWritten() ==
        old(wr.GetDataWritten()) +
        UInt16ToSeq(n as uint16) +
        Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j);
      invariant totalWritten == 2 + |Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j)|
    {
      var entry := encryptedDataKeys.entries[j];

      len := wr.WriteUInt16(|entry.providerID| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(entry.providerID);
      totalWritten := totalWritten + len;

      len := wr.WriteUInt16(|entry.providerInfo| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(entry.providerInfo);
      totalWritten := totalWritten + len;

      len := wr.WriteUInt16(|entry.ciphertext| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(entry.ciphertext);
      totalWritten := totalWritten + len;

      j := j + 1;
    }

    return Success(totalWritten);
  }
}
