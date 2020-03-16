include "MessageHeader.dfy"
include "Materials.dfy"
include "AlgorithmSuite.dfy"
include "../Util/UTF8.dfy"
include "../Util/Sets.dfy"


include "../Util/Streams.dfy"
include "../StandardLibrary/StandardLibrary.dfy"

module Serialize {
  import Msg = MessageHeader
  import AlgorithmSuite

  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import UTF8
  import Sets

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

    len := SerializeEDKs(wr, hb.encryptedDataKeys);
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

    var kvPairsLength := Msg.ComputeKVPairsLength(kvPairs);
    var len := wr.WriteUInt16(kvPairsLength as uint16);

    totalWritten := totalWritten + len;

    len :- SerializeKVPairs(wr, kvPairs);
    totalWritten := totalWritten + len;

    return Success(totalWritten);
  }

  // ----- SerializeKVPairs -----

  method SerializeKVPairs(wr: Streams.ByteWriter, encryptionContext: Materials.EncryptionContext) returns (ret: Result<nat>)
    requires wr.Valid() && Msg.ValidKVPairs(encryptionContext)
    modifies wr.writer`data
    ensures wr.Valid() && Msg.ValidKVPairs(encryptionContext)
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := Msg.KVPairsToSeq(encryptionContext);
        var initLen := old(wr.GetSizeWritten());
        && totalWritten == |serAAD|
        && initLen + totalWritten == wr.GetSizeWritten()
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD
      case Failure(e) => true
  {
    var totalWritten := 0;

    if |encryptionContext| == 0 {
      return Success(totalWritten);
    }

    var len := wr.WriteUInt16(|encryptionContext| as uint16);
    totalWritten := totalWritten + len;

    // Serialization is easier to implement and verify by first converting the map to
    // a sequence of pairs.
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));

    var j := 0;
    ghost var n := |kvPairs|;
    while j < |kvPairs|
      invariant j <= n == |kvPairs|
      invariant wr.GetDataWritten() ==
        old(wr.GetDataWritten()) +
        UInt16ToSeq(n as uint16) +
        Msg.KVPairEntriesToSeq(kvPairs, 0, j)
      invariant totalWritten == 2 + |Msg.KVPairEntriesToSeq(kvPairs, 0, j)|
    {
      ghost var previouslyWritten := wr.GetDataWritten();

      len := wr.WriteUInt16(|kvPairs[j].0| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(kvPairs[j].0);
      totalWritten := totalWritten + len;

      len := wr.WriteUInt16(|kvPairs[j].1| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(kvPairs[j].1);
      totalWritten := totalWritten + len;

      calc {
        wr.GetDataWritten();
      ==  // the four writes in this loop iteration write Msg.KVPairToSeq(kvPairs[j])
        previouslyWritten + Msg.KVPairToSeq(kvPairs[j]);
      ==  // loop invariant on entry to loop
        (old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16) + Msg.KVPairEntriesToSeq(kvPairs, 0, j)) + Msg.KVPairToSeq(kvPairs[j]);
      ==  // + is associative
        old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16) + (Msg.KVPairEntriesToSeq(kvPairs, 0, j) + Msg.KVPairToSeq(kvPairs[j]));
      ==  { assert Msg.KVPairEntriesToSeq(kvPairs, 0, j) + Msg.KVPairToSeq(kvPairs[j]) == Msg.KVPairEntriesToSeq(kvPairs, 0, j + 1); }
        old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16) + Msg.KVPairEntriesToSeq(kvPairs, 0, j + 1);
      }

      j := j + 1;
    }

    return Success(totalWritten);
  }

  // ----- SerializeEDKs -----

  method SerializeEDKs(wr: Streams.ByteWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: nat)
    requires wr.Valid() && encryptedDataKeys.Valid()
    modifies wr.writer`data
    ensures wr.Valid() && encryptedDataKeys.Valid()
    ensures ret == |Msg.EDKsToSeq(encryptedDataKeys)|
    ensures old(wr.GetSizeWritten()) + ret == wr.GetSizeWritten()
    ensures wr.GetDataWritten() == old(wr.GetDataWritten()) + Msg.EDKsToSeq(encryptedDataKeys)
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

    return totalWritten;
  }
}
