// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "MessageHeader.dfy"
include "Materials.dfy"
include "EncryptionContext.dfy"
include "AlgorithmSuite.dfy"

include "../Util/Streams.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../Util/UTF8.dfy"

/*
 * The message header deserialization
 *
 * The message header is deserialized from a uint8 stream.
 * When encountering an error, we stop and return it immediately, leaving the remaining inputs on the stream
 */
module Deserialize {
  export
    provides DeserializeHeader, Materials
    provides Streams, StandardLibrary, UInt, AlgorithmSuite, Msg
    provides InsertNewEntry, UTF8, EncryptionContext

  import Msg = MessageHeader

  import AlgorithmSuite
  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Materials
  import EncryptionContext


  method DeserializeHeader(rd: Streams.ByteReader) returns (res: Result<Msg.Header>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res
      case Success(header) => header.Valid()
        && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
        && exists hbSeq | hbSeq + header.auth.iv + header.auth.authenticationTag == rd.reader.data[old(rd.reader.pos)..rd.reader.pos] ::
          Msg.SeqToHeaderBody(hbSeq, header.body)
      case Failure(_) => true
  {
    var hb :- DeserializeHeaderBody(rd);
    var auth :- DeserializeHeaderAuthentication(rd, hb.algorithmSuiteID);
    return Success(Msg.Header(hb, auth));
  }

  /**
  * Reads raw header data from the input stream and populates the header with all of the information about the
  * message.
  */
  method DeserializeHeaderBody(rd: Streams.ByteReader) returns (ret: Result<Msg.HeaderBody>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(hb) => 
        && hb.Valid()
        && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
        && Msg.SeqToHeaderBody(rd.reader.data[old(rd.reader.pos)..rd.reader.pos], hb)
      case Failure(_) => true
  {
    var version :- DeserializeVersion(rd);
    var typ :- DeserializeType(rd);
    var algorithmSuiteID :- DeserializeAlgorithmSuiteID(rd);
    var messageID :- DeserializeMsgID(rd);
    var aad :- DeserializeAAD(rd);
    var encryptedDataKeys :- DeserializeEncryptedDataKeys(rd);
    var contentType :- DeserializeContentType(rd);
    var _ :- DeserializeReserved(rd);
    var ivLength :- rd.ReadByte();
    var frameLength :- rd.ReadUInt32();

    // inter-field checks
    if ivLength as nat != algorithmSuiteID.IVLength() {
      return Failure("Deserialization Error: Incorrect IV length.");
    }
    if contentType.NonFramed? && frameLength != 0 {
      return Failure("Deserialization Error: Frame length must be 0 when content type is non-framed.");
    } else if contentType.Framed? && frameLength == 0 {
      return Failure("Deserialization Error: Frame length must be non-0 when content type is framed.");
    }

    reveal Msg.SeqToHeaderBody();
    var hb := Msg.HeaderBody(
      version,
      typ,
      algorithmSuiteID,
      messageID,
      aad,
      encryptedDataKeys,
      contentType,
      ivLength,
      frameLength);
    assert Msg.SeqToHeaderBody(rd.reader.data[old(rd.reader.pos)..rd.reader.pos], hb);
    return Success(hb);
  }

  /*
   * Reads IV length and auth tag of the lengths specified by algorithmSuiteID.
   */
  method DeserializeHeaderAuthentication(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<Msg.HeaderAuthentication>)
    requires rd.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(ha) =>
        var bytesRead := algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength();
        var serHa := ha.iv + ha.authenticationTag;
        && |ha.iv| == algorithmSuiteID.IVLength()
        && |ha.authenticationTag| == algorithmSuiteID.TagLength()
        && old(rd.reader.pos) + bytesRead == rd.reader.pos
        && serHa == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    var authenticationTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    return Success(Msg.HeaderAuthentication(iv, authenticationTag));
  }

  /*
   * Methods for deserializing pieces of the message header.
   */
  method DeserializeVersion(rd: Streams.ByteReader) returns (ret: Result<Msg.Version>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(ver) =>
        var bytesRead := 1;
        var serVer := [ver as uint8];
        && old(rd.reader.pos) + bytesRead == rd.reader.pos
        && serVer == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var version :- rd.ReadByte();
    if version == Msg.VERSION_1 {
      return Success(version);
    } else {
      return Failure("Deserialization Error: Version not supported.");
    }
  }

  method DeserializeType(rd: Streams.ByteReader) returns (ret: Result<Msg.Type>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(typ) =>
        var bytesRead := 1;
        var serTyp := [typ as uint8];
        && old(rd.reader.pos) + bytesRead == rd.reader.pos
        && serTyp == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var typ :- rd.ReadByte();
    if typ == Msg.TYPE_CUSTOMER_AED {
      return Success(typ);
    } else {
      return Failure("Deserialization Error: Type not supported.");
    }
  }

  method DeserializeAlgorithmSuiteID(rd: Streams.ByteReader) returns (ret: Result<AlgorithmSuite.ID>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(algID) =>
        var bytesRead := 2;
        var serAlgID := UInt16ToSeq(algID as uint16);
        && old(rd.reader.pos) + bytesRead == rd.reader.pos
        && serAlgID == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var algorithmSuiteID :- rd.ReadUInt16();
    if algorithmSuiteID in AlgorithmSuite.VALID_IDS {
      return Success(algorithmSuiteID as AlgorithmSuite.ID);
    } else {
      return Failure("Deserialization Error: Algorithm suite not supported.");
    }
  }

  method DeserializeMsgID(rd: Streams.ByteReader) returns (ret: Result<Msg.MessageID>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(messageID) =>
        var bytesRead := |messageID|;
        var sermessageID := messageID;
        && old(rd.reader.pos) + bytesRead == rd.reader.pos
        && sermessageID == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
    
  {
    var msgID: seq<uint8> :- rd.ReadBytes(Msg.MESSAGE_ID_LEN);
    return Success(msgID);
  }

  method DeserializeUTF8(rd: Streams.ByteReader, n: nat) returns (ret: Result<UTF8.ValidUTF8Bytes>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures ret.Success? ==> var expectedRes := EncryptionContext.GetUTF8(rd.reader.data[old(rd.reader.pos)..], n);
      expectedRes.Some? && expectedRes.get == ret.value
    ensures match ret
      case Success(bytes) =>
        && UTF8.ValidUTF8Seq(bytes)
        && old(rd.reader.pos) + n == rd.reader.pos
        && bytes == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var bytes :- rd.ReadBytes(n);
    if UTF8.ValidUTF8Seq(bytes) {
      var utf8: UTF8.ValidUTF8Bytes := bytes; 
      assert bytes == rd.reader.data[old(rd.reader.pos)..][..n];
      return Success(utf8);
    } else {
      return Failure("Deserialization Error: Not a valid UTF8 string.");
    }
  }

  /**
    DeserializeAAD is not a perfect dual of SerializeAAD
    A Map of key value pairs is deserialized. The map can only be created from a sequence of sorted and unqiue pairs
    SerializeAAD creates a sequence of sorted unique pairs, Deserialize reads any sequence of pairs and sorts them before creating a Map
    Deserialize is not an injective function so there is no inverse function (a Dual serialize).
    To still prove a duality we could define a weaker Serialization which is not a function but a relation between Maps and sequences (EncryptionContext.LinearSeqToMap)
    We now prove that EncryptionContext.LinearSeqToMap(DeserializeAAD(seq), seq) which means any map we deserialize from a sequence is in the weak serialize relation
    Furthermore we prove that EncryptionContext.LinearSeqToMap(map, SerializeAAD(map)) which means that any map we serialize to a sequence is in the weak serialize relation 
    From this we can conclude that DeserializeAAD(SerializeAAD(map)) == map
   */
  method DeserializeAAD(rd: Streams.ByteReader) returns (ret: Result<EncryptionContext.Map>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(aad) => 
        EncryptionContext.Serializable(aad)
        && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
        && EncryptionContext.LinearSeqToMap(rd.reader.data[old(rd.reader.pos)..rd.reader.pos], aad)
      case Failure(_) => true
  {
    reveal EncryptionContext.Serializable();
    
    var kvPairsLength :- rd.ReadUInt16();
    if kvPairsLength == 0 {
      return Success(map[]);
    } else if kvPairsLength < 2 {
      return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
    }
    var totalBytesRead := 0;

    var kvPairsCount :- rd.ReadUInt16();
    totalBytesRead := totalBytesRead + 2;
    if kvPairsCount == 0 {
      return Failure("Deserialization Error: Key value pairs count is 0.");
    }

    // Building a map item by item is expensive in dafny, so
    // instead we first read the key value pairs into a sequence
    var kvPairs: EncryptionContext.Linear := [];
    var i := 0;
    ghost var startKvPos := rd.reader.pos;
    ghost var unsortedKvPairs: EncryptionContext.Linear := [];

    while i < kvPairsCount
      invariant startKvPos <= rd.reader.pos
      invariant rd.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant |kvPairs| == |unsortedKvPairs|
      invariant forall kvPair :: kvPair in kvPairs <==> kvPair in unsortedKvPairs
      invariant totalBytesRead == 2 + EncryptionContext.LinearLength(kvPairs, 0, i as nat) <= kvPairsLength as nat
      invariant totalBytesRead == |rd.reader.data[old(rd.reader.pos)..rd.reader.pos]| - 2
      invariant EncryptionContext.SerializableLinear(kvPairs)
      invariant EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs)
      invariant rd.reader.data[startKvPos..rd.reader.pos] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|)
    {
      ghost var oldPosPair := rd.reader.pos;
      ghost var oldKvPairs := kvPairs;
      ghost var oldunsortedKvPairs := unsortedKvPairs;

      var keyLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      
      var key :- DeserializeUTF8(rd, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;
      
      var valueLength :- rd.ReadUInt16();
          
      totalBytesRead := totalBytesRead + 2;
      // check that we're not exceeding the stated AAD length
      if kvPairsLength as nat < totalBytesRead + valueLength as nat {
        return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
      }

      var value :- DeserializeUTF8(rd, valueLength as nat);
      totalBytesRead := totalBytesRead + |value|;
      
      // We want to keep entries sorted by key. We don't insist that the entries be sorted
      // already, but we do insist there are no duplicate keys.
      var opt, insertionPoint := InsertNewEntry(kvPairs, key, value);

      match opt {
        case Some(kvPairs_) =>
          EncryptionContext.LinearInsert(kvPairs, insertionPoint, key, value);
          kvPairs := kvPairs_;
          unsortedKvPairs := unsortedKvPairs + [(key, value)];
        case None =>
          return Failure("Deserialization Error: Duplicate key.");
      }
      
      i := i + 1;
      
      // Proof that a KVPair is deserialized correctly
      // Note: Proof that serializing the resulting pair is equal to the input is easier and more stable.
      assert EncryptionContext.KVPairToSeq((key, value)) == rd.reader.data[oldPosPair .. rd.reader.pos] by {
        assert rd.reader.data[oldPosPair .. rd.reader.pos] == rd.reader.data[oldPosPair..oldPosPair + 4 + |key| + |value|];
        assert UInt16ToSeq(|key| as uint16) == rd.reader.data[oldPosPair..oldPosPair + 2];
        assert key == rd.reader.data[oldPosPair + 2..oldPosPair + 2 + |key|];
        assert UInt16ToSeq(|value| as uint16) == rd.reader.data[oldPosPair + 2 + |key|..oldPosPair + 2 + |key| + 2];
        assert value == rd.reader.data[oldPosPair + 4 + |key|..oldPosPair + 4 + |key| + |value|];
      }
      
      assert forall p :: (p in oldKvPairs || p == (key, value)) <==> p in kvPairs;

      // The unsorted sequence of pairs can be serialized to the bytes read from the stream
      assert rd.reader.data[startKvPos..rd.reader.pos] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) by {
        EncryptionContext.LinearToUnorderedSeqInductiveStep(oldunsortedKvPairs, [(key, value)], 0 , |oldunsortedKvPairs|);
        assert EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs| - 1) == rd.reader.data[startKvPos..oldPosPair];
        assert EncryptionContext.KVPairToSeq(unsortedKvPairs[|unsortedKvPairs| - 1]) == rd.reader.data[oldPosPair .. rd.reader.pos];
          assert rd.reader.data[startKvPos..rd.reader.pos] == rd.reader.data[startKvPos..oldPosPair] + rd.reader.data[oldPosPair..rd.reader.pos];
      }  
    }
    if kvPairsLength as nat != totalBytesRead {
      return Failure("Deserialization Error: Bytes actually read differs from bytes supposed to be read.");
    }

    // Since we are using an extern to convert the sequence to a map,
    // we must check after the extern call that the map is valid for AAD.
    // If not valid, then something was wrong with the conversion, as
    // failures for invalid serializations should be caught earlier.
    var encryptionContext: map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes> := EncryptionContext.LinearToMap(kvPairs);
    var isValid := EncryptionContext.CheckSerializable(encryptionContext);
    if !isValid || |kvPairs| != |encryptionContext| {
      return Failure("Deserialization Error: Failed to parse encryption context.");
    }
    
    SerializationIsValid(rd.reader.data[old(rd.reader.pos)..rd.reader.pos], encryptionContext, unsortedKvPairs, kvPairs);
    
    return Success(encryptionContext);
  }

  // Lemma used for validation speedup, Combines straightforward facts into the post condition
  lemma SerializationIsValid(sequence: seq<uint8>, resultMap: EncryptionContext.Map, unsortedKvPairs: EncryptionContext.Linear, kvPairs: EncryptionContext.Linear)
    requires |resultMap| == 0 ==> |sequence| == 2
    requires |resultMap| != 0 ==> 4 <= |sequence|
    requires EncryptionContext.Serializable(resultMap)
    requires |resultMap| == |kvPairs| == |unsortedKvPairs|
    requires forall kvPair :: kvPair in kvPairs <==> kvPair in unsortedKvPairs
    requires EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs)
    requires EncryptionContext.SerializableLinear(kvPairs)
    requires reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(resultMap) && EncryptionContext.SerializableLinear(kvPairs) ==> 
      EncryptionContext.MapToSeq(resultMap) == if |resultMap| == 0 then [] else UInt16ToSeq(|kvPairs| as uint16) + EncryptionContext.LinearToSeq(kvPairs, 0, |kvPairs|)
    requires |sequence[2..]| < UINT16_LIMIT && sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16)
    requires |resultMap| != 0 ==> sequence[2..][..2] == UInt16ToSeq(|resultMap| as uint16);
    requires |resultMap| != 0 ==> sequence[4..] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|)   
    ensures EncryptionContext.LinearSeqToMap(sequence, resultMap)
  {
    reveal EncryptionContext.Serializable();
    if |resultMap| == 0 {
      
    } else {
      assert EncryptionContext.LinearSeqToMap(sequence, resultMap) by {
        assert EncryptionContext.SeqToMap(sequence[2..], resultMap) by {
          EncryptionContext.InsertionSortPreservesProperties(unsortedKvPairs);
          // This is the line which ties the kvPairs and unstoredkvPairs together, since all pairs are unqiue and they contain the same pairs
          // There is only one sorted sequence, so sorting the unsorted pairs gives us kvPairs
          EncryptionContext.SortedSequenceIsUnqiue(kvPairs, EncryptionContext.InsertionSort(unsortedKvPairs));
          
          assert EncryptionContext.SeqToLinearToMap(sequence[2..], resultMap, unsortedKvPairs, kvPairs) by 
          { 
            assert 2 <= |sequence[2..]|;
            assert EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs);
            assert EncryptionContext.SerializableLinear(kvPairs);
            assert EncryptionContext.SerializableKVPairs(resultMap);
            assert sequence[2..][..2] == UInt16ToSeq(|resultMap| as uint16); 
            assert EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) == sequence[2..][2..];
            assert kvPairs == EncryptionContext.InsertionSort(unsortedKvPairs);
            assert EncryptionContext.MapToSeq(resultMap) == sequence[2..][..2] + EncryptionContext.LinearToSeq(kvPairs, 0, |kvPairs|);
          }
          assert sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16);
        }
      }
    }
  }


  method InsertNewEntry(kvPairs: EncryptionContext.Linear, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
      returns (res: Option<EncryptionContext.Linear>, ghost insertionPoint: nat)
    requires EncryptionContext.LinearSorted(kvPairs)
    requires forall i, j | 0 <= i < j < |kvPairs| :: kvPairs[i].0 != kvPairs[j].0
    ensures (exists l | l in kvPairs :: key == l.0) <==> res.None?
    ensures match res
      case None =>
        (exists i :: 0 <= i < |kvPairs| && kvPairs[i].0 == key)  // key already exists
      case Some(kvPairs') =>
        && insertionPoint <= |kvPairs|
        && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]
        && EncryptionContext.LinearSorted(kvPairs')
        && (forall i, j | 0 <= i < j < |kvPairs'| :: kvPairs'[i].0 != kvPairs'[j].0)
  {
    var n := |kvPairs|;
    while 0 < n && LexicographicLessOrEqual(key, kvPairs[n - 1].0, UInt.UInt8Less)
      invariant 0 <= n <= |kvPairs|
      invariant forall i :: n <= i < |kvPairs| ==> LexicographicLessOrEqual(key, kvPairs[i].0, UInt.UInt8Less)
      invariant forall i | n < i < |kvPairs| :: kvPairs[i].0 != key
    {
      n := n - 1;
    }

    EncryptionContext.LinearSortedImpliesStrongLinearSorted(kvPairs);
    if kvPairs != [] && LexicographicLessOrEqual(key, kvPairs[|kvPairs| - 1].0, UInt.UInt8Less) && kvPairs[n].0 == key {
      return None, n;
    } else {
      var kvPairs' := kvPairs[..n] + [(key, value)] + kvPairs[n..];
      
      if 0 < n {
        LexIsTotal(kvPairs'[n - 1].0, kvPairs'[n].0, UInt.UInt8Less);
      }
      return Some(kvPairs'), n;
    }

  }

  method DeserializeEncryptedDataKeys(rd: Streams.ByteReader) returns (ret: Result<Msg.EncryptedDataKeys>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(edks) => 
        edks.Valid()
        && var n := |Msg.EDKsToSeq(edks)|;
        old(rd.reader.pos) + n == rd.reader.pos
        && Msg.EDKsToSeq(edks) == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var edkCount :- rd.ReadUInt16();
    if edkCount == 0 {
      return Failure("Deserialization Error: Encrypted data key count is 0.");
    }
    
    assert rd.reader.pos == old(rd.reader.pos) + 2;
    var edkEntries: seq<Materials.EncryptedDataKey> := [];
    var i := 0;
    while i < edkCount
      invariant old(rd.reader.pos) + 2 <= rd.reader.pos
      invariant rd.Valid()
      invariant i <= edkCount
      invariant |edkEntries| == i as int
      invariant forall i :: 0 <= i < |edkEntries| ==> edkEntries[i].Valid()
      invariant Msg.EDKEntriesToSeq(edkEntries, 0, |edkEntries|) == rd.reader.data[old(rd.reader.pos) + 2 .. rd.reader.pos]
    {
      ghost var invStartPos := rd.reader.pos;
      // Key provider ID
      var keyProviderIDLength :- rd.ReadUInt16();
      var str :- DeserializeUTF8(rd, keyProviderIDLength as nat);
      var keyProviderID := str;

      // Key provider info
      var keyProviderInfoLength :- rd.ReadUInt16();
      var keyProviderInfo :- rd.ReadBytes(keyProviderInfoLength as nat);

      // Encrypted data key
      var edkLength :- rd.ReadUInt16();
      var edk :- rd.ReadBytes(edkLength as nat);

      edkEntries := edkEntries + [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)];
      i := i + 1;
      assert invStartPos < rd.reader.pos;
      assert Msg.EDKEntriesToSeq(edkEntries, 0, |edkEntries|) == rd.reader.data[old(rd.reader.pos) + 2 .. rd.reader.pos] by {
        assert Msg.EDKEntryToSeq(Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)) == rd.reader.data[invStartPos..rd.reader.pos];
        Msg.EDKEntriesToSeqInductiveStep(edkEntries[..|edkEntries| - 1], 
          [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)], 0, |edkEntries[..|edkEntries| - 1]|); 
      }
    }
    assert |edkEntries| == edkCount as int; 
    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(rd: Streams.ByteReader) returns (ret: Result<Msg.ContentType>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(contentType) =>
        old(rd.reader.pos) + 1 == rd.reader.pos
        && [Msg.ContentTypeToUInt8(contentType)] == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var byte :- rd.ReadByte();
    match Msg.UInt8ToContentType(byte)
    case None =>
      return Failure("Deserialization Error: Content type not supported.");
    case Some(contentType) =>
      return Success(contentType);
  }

  method DeserializeReserved(rd: Streams.ByteReader) returns (ret: Result<seq<uint8>>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(contnetType) =>
        old(rd.reader.pos) + 4 == rd.reader.pos
        && Msg.Reserved == rd.reader.data[old(rd.reader.pos)..rd.reader.pos]
      case Failure(_) => true
  {
    var reserved :- rd.ReadBytes(4);
    if reserved == Msg.Reserved {
      return Success(reserved);
    } else {
      return Failure("Deserialization Error: Reserved fields must be 0.");
    }
  }
}
