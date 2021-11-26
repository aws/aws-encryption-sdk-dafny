// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "MessageHeader.dfy"
include "EncryptionContext.dfy"
include "../Util/UTF8.dfy"
include "../Util/Sets.dfy"
include "../Util/Streams.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "Serialize/SerializableTypes.dfy"

module Serialize {
  import Msg = MessageHeader
  import EncryptionContext
  import opened SerializableTypes

  import Streams
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Sets

  method SerializeHeaderBody(wr: Streams.ByteWriter, hb: Msg.HeaderBody) returns (ret: Result<nat, string>)
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

  method SerializeHeaderAuthentication(wr: Streams.ByteWriter, ha: Msg.HeaderAuthentication) returns (ret: Result<nat, string>)
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
        && old(wr.GetDataWritten()) + serHa == wr.GetDataWritten()
      case Failure(e) => true
  {
    var m := wr.WriteBytes(ha.iv);
    var n := wr.WriteBytes(ha.authenticationTag);
    return Success(m + n);
  }

  // ----- SerializeAAD -----

  method SerializeAAD(wr: Streams.ByteWriter, kvPairs: EncryptionContext.Map) returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.Serializable(kvPairs)
    modifies wr.writer`data
    ensures wr.Valid() && EncryptionContext.Serializable(kvPairs)
    ensures match ret
      case Success(totalWritten) =>
        var serAAD := EncryptionContext.MapToLinear(kvPairs);
        var initLen := old(wr.GetSizeWritten());
        && totalWritten == |serAAD|
        && initLen + totalWritten == wr.GetSizeWritten()
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD
      case Failure(e) => true
  {
    reveal EncryptionContext.Serializable(), EncryptionContext.MapToLinear();
    var totalWritten := 0;

    var kvPairsLength := EncryptionContext.ComputeLength(kvPairs);
    var len := wr.WriteUInt16(kvPairsLength as uint16);

    totalWritten := totalWritten + len;

    len :- SerializeKVPairs(wr, kvPairs);
    totalWritten := totalWritten + len;

    return Success(totalWritten);
  }

  // ----- SerializeKVPairs -----

  method SerializeKVPairs(wr: Streams.ByteWriter, encryptionContext: EncryptionContext.Map) returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.SerializableKVPairs(encryptionContext)
    modifies wr.writer`data
    ensures wr.Valid() && EncryptionContext.SerializableKVPairs(encryptionContext)
    ensures match ret
      case Success(newlyWritten) =>
        var serAAD := EncryptionContext.MapToSeq(encryptionContext);
        && newlyWritten == |serAAD|
        && wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD
      case Failure(e) => true
  {
    var newlyWritten := 0;

    if |encryptionContext| == 0 {
      assert {:focus} true;
      return Success(newlyWritten);
    }

    assert {:focus} true;
    var len := wr.WriteUInt16(|encryptionContext| as uint16);
    newlyWritten := newlyWritten + len;

    // Serialization is easier to implement and verify by first converting the map to
    // a sequence of pairs.
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    ghost var kvPairs := seq(|keys|, i requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));

    ghost var n := |keys|;
    ghost var writtenBeforeLoop := wr.GetDataWritten();
    assert writtenBeforeLoop == old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16);

    var j := 0;
    while j < |keys|
      invariant j <= n == |keys|
      invariant wr.GetDataWritten() == writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j)
      invariant wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten
    {
      assert {:focus} true;
      len :- SerializeKVPair(wr, keys[j], encryptionContext[keys[j]]);
      newlyWritten := newlyWritten + len;
      assert wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten;

      calc {
        wr.GetDataWritten();
      ==  // by the loop invariant and the postcondition of SerializeKVPair
        writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]);
      ==  // + is associative
        writtenBeforeLoop + (EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]));
      ==  { assert EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]) == EncryptionContext.LinearToSeq(kvPairs, 0, j + 1); }
        writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j + 1);
      }

      j := j + 1;
    }

    assert {:focus} true;
    assert EncryptionContext.MapToSeq(encryptionContext) == UInt16ToSeq(n as uint16) + EncryptionContext.LinearToSeq(kvPairs, 0, j) by {
      assert {:focus} true;
      assert |kvPairs| == j;
    }
    return Success(newlyWritten);
  }

  method SerializeKVPair(wr: Streams.ByteWriter, k: UTF8.ValidUTF8Bytes, v: UTF8.ValidUTF8Bytes) returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.SerializableKVPair((k, v))
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret
      case Success(newlyWritten) =>
        var serKV := EncryptionContext.KVPairToSeq((k, v));
        && newlyWritten == |serKV|
        && wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten
        && wr.GetDataWritten() == old(wr.GetDataWritten()) + serKV
      case Failure(e) => true
  {
    ghost var previouslyWritten := wr.GetDataWritten();
    var newlyWritten := 0;

    var len := wr.WriteUInt16(|k| as uint16);
    newlyWritten := newlyWritten + len;

    len := wr.WriteBytes(k);
    newlyWritten := newlyWritten + len;

    len := wr.WriteUInt16(|v| as uint16);
    newlyWritten := newlyWritten + len;

    len := wr.WriteBytes(v);
    newlyWritten := newlyWritten + len;

    calc {
      wr.GetDataWritten();
    ==  // the four writes in the loop body
      previouslyWritten + UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v;
    ==  // associativity +
      previouslyWritten + (UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);
    ==  // def. EncryptionContext.KVPairToSeq
      previouslyWritten + EncryptionContext.KVPairToSeq((k, v));
    }

    return Success(newlyWritten);
  }

  // ----- SerializeEDKs -----

  method SerializeEDKs(wr: Streams.ByteWriter, encryptedDataKeys: ESDKEncryptedDataKeys) returns (ret: nat)
    requires wr.Valid()
    modifies wr.writer`data
    ensures wr.Valid()
    ensures ret == |Msg.EDKsToSeq(encryptedDataKeys)|
    ensures old(wr.GetSizeWritten()) + ret == wr.GetSizeWritten()
    ensures wr.GetDataWritten() == old(wr.GetDataWritten()) + Msg.EDKsToSeq(encryptedDataKeys)
  {
    var totalWritten := 0;

    var len := wr.WriteUInt16(|encryptedDataKeys| as uint16);
    totalWritten := totalWritten + len;

    var j := 0;
    ghost var n := |encryptedDataKeys|;
    while j < |encryptedDataKeys|
      invariant j <= n == |encryptedDataKeys|
      invariant wr.GetDataWritten() ==
        old(wr.GetDataWritten()) +
        UInt16ToSeq(n as uint16) +
        Msg.EDKEntriesToSeq(encryptedDataKeys, 0, j);
      invariant totalWritten == 2 + |Msg.EDKEntriesToSeq(encryptedDataKeys, 0, j)|
    {
      var entry := encryptedDataKeys[j];

      len := wr.WriteUInt16(|entry.keyProviderId| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(entry.keyProviderId);
      totalWritten := totalWritten + len;

      len := wr.WriteUInt16(|entry.keyProviderInfo| as uint16);
      totalWritten := totalWritten + len;

      len := wr.WriteBytes(entry.keyProviderInfo);
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
