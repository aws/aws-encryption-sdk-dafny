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
        //var serHb := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(hb));
        //var initLen := old(rd.GetSizeWritten());
        hb.Valid()
        //&& totalWritten == |serHb|
        //&& initLen + totalWritten == wr.GetSizeWritten()
        //&& serHb == wr.GetDataWritten()[initLen..initLen + totalWritten]
        
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

  method DeserializeAAD(rd: Streams.ByteReader) returns (ret: Result<EncryptionContext.Map>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret
      case Success(aad) => 
        EncryptionContext.Serializable(aad)
        && old(rd.reader.pos) <= rd.reader.pos
        && var mapRes := EncryptionContext.SeqToMap(rd.reader.data[old(rd.reader.pos)..rd.reader.pos]);
        mapRes.Some?
        && mapRes.get == aad 
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
    ghost var pairToSequenceMap: seq<(seq<uint8>, (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes))> := [];

    while i < kvPairsCount
      invariant startKvPos <= rd.reader.pos
      invariant rd.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant totalBytesRead == 2 + EncryptionContext.LinearLength(kvPairs, 0, i as nat) <= kvPairsLength as nat
      invariant EncryptionContext.LinearSorted(kvPairs)
      invariant EncryptionContext.LinearIsUnique(kvPairs)
      invariant forall pair | pair in pairToSequenceMap :: EncryptionContext.SeqToKVPair(pair.0) == Some((pair.1, []))
      // invariant EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..rd.reader.pos], []) == Some(kvPairs)
    {
      ghost var oldPosPair := rd.reader.pos;
      ghost var oldKvPairs := kvPairs;
      var keyLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;

      var key :- DeserializeUTF8(rd, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;
      assert key  == EncryptionContext.GetUTF8(rd.reader.data[oldPosPair + 2..], keyLength as nat).get;
      
      var valueLength :- rd.ReadUInt16();
          
      totalBytesRead := totalBytesRead + 2;
      // check that we're not exceeding the stated AAD length
      if kvPairsLength as nat < totalBytesRead + valueLength as nat {
        return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
      }

      var valueSeq :- DeserializeUTF8(rd, valueLength as nat);
      var value: UTF8.ValidUTF8Bytes := valueSeq;
      totalBytesRead := totalBytesRead + |value|;
      assert value == EncryptionContext.GetUTF8(rd.reader.data[oldPosPair + 4 + keyLength as nat..], valueLength as nat).get;
      
      // We want to keep entries sorted by key. We don't insist that the entries be sorted
      // already, but we do insist there are no duplicate keys.
      var opt, insertionPoint := InsertNewEntry(kvPairs, key, value);
      
      assert EncryptionContext.InsertPairMock((key, value), kvPairs) == opt by {
        var expectedOpt := EncryptionContext.InsertPairMock((key, value), kvPairs);
        if opt.Some? {
          assert expectedOpt.Some?;
          EncryptionContext.SortedSequenceIsUnqiue(opt.get,expectedOpt.get);
        }else{
          assert expectedOpt.None?;
        }
      }

      match opt {
        case Some(kvPairs_) =>
          EncryptionContext.LinearInsert(kvPairs, insertionPoint, key, value);
          kvPairs := kvPairs_;
        case None =>
          return Failure("Deserialization Error: Duplicate key.");
      }
      assert valueLength == SeqToUInt16(rd.reader.data[oldPosPair + 2 + keyLength as int.. oldPosPair + 4 + keyLength as int]);

      i := i + 1;
      
      // Proof that a KVPair is deserialized correctly
      // Note: Proof that serializing the resulting pair is equal to the input is easier and more stable.
      // We use the duality between serialize and deserialize to prove that deserialize also holds. This is more robust then proving deserialize directly 
      assert EncryptionContext.KVPairToSeq((key, value)) == rd.reader.data[oldPosPair .. rd.reader.pos];
      EncryptionContext.KVPairToSeqIsDualSeqToKVPair((key, value), []);
      assert rd.reader.data[oldPosPair..rd.reader.pos] + [] == rd.reader.data[oldPosPair..rd.reader.pos]; // Statement is needed
      assert EncryptionContext.SeqToKVPair(rd.reader.data[oldPosPair..rd.reader.pos]) == Some(((key, value), []));
      pairToSequenceMap := pairToSequenceMap + [(rd.reader.data[oldPosPair..rd.reader.pos], (key, value))];

      assert forall p :: (p in oldKvPairs || p == (key, value)) <==> p in kvPairs;
      
      assert EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..rd.reader.pos], []) == Some(kvPairs) by {
        var expectedOpt := EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..rd.reader.pos], []);
        assert expectedOpt.Some?;
        EncryptionContext.SortedSequenceIsUnqiue(kvPairs, expectedOpt.get);
      }
      

      // ghost var expectedkvPairs := EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..rd.reader.pos], []);
      // assert EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..rd.reader.pos], []) == Some(kvPairs) by {

      //   assert rd.reader.data[startKvPos..rd.reader.pos] == rd.reader.data[startKvPos..oldPosPair] + rd.reader.data[oldPosPair .. rd.reader.pos] by {
      //     assume rd.reader.data[startKvPos..rd.reader.pos] == rd.reader.data[startKvPos..oldPosPair] + rd.reader.data[oldPosPair .. rd.reader.pos];
      //   }
      //   assert EncryptionContext.SeqToLinear(rd.reader.data[startKvPos..oldPosPair], []) == Some(oldKvPairs);
      //   assert Some(kvPairs) == EncryptionContext.InsertPairMock((key, value), oldKvPairs);
      
      // }         

        
        /**
          if sequence == [] then Some(linear) else
            var resHead := SeqToKVPair(sequence); 
            if resHead.Some? then 
              var newLinear := InsertPairMock(resHead.get.0, linear);
              if newLinear.Some? then
                SeqToLinear(resHead.get.1, newLinear.get)
              else
                None // Duplicate key
            else
              None // Too short      
         */
        
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
    if !isValid {
      return Failure("Deserialization Error: Failed to parse encryption context.");
    }

    return Success(encryptionContext);
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
        // Old spec
        && insertionPoint <= |kvPairs|
        && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]
        && EncryptionContext.LinearSorted(kvPairs')
        && (forall i, j | 0 <= i < j < |kvPairs'| :: kvPairs'[i].0 != kvPairs'[j].0)
      // ensures EncryptionContext.InsertPairMock((key, value), kvPairs)
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
      EncryptionContext.InsertFailsOnDuplicate(kvPairs, (key, value));
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
      case Success(edks) => edks.Valid()
      case Failure(_) => true
  {
    var edkCount :- rd.ReadUInt16();
    if edkCount == 0 {
      return Failure("Deserialization Error: Encrypted data key count is 0.");
    }

    var edkEntries: seq<Materials.EncryptedDataKey> := [];
    var i := 0;
    while i < edkCount
      invariant rd.Valid()
      invariant i <= edkCount
      invariant |edkEntries| == i as int
      invariant forall i :: 0 <= i < |edkEntries| ==> edkEntries[i].Valid()
    {
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
    }

    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(rd: Streams.ByteReader) returns (ret: Result<Msg.ContentType>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
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
  {
    var reserved :- rd.ReadBytes(4);
    if reserved == Msg.Reserved {
      return Success(reserved);
    } else {
      return Failure("Deserialization Error: Reserved fields must be 0.");
    }
  }
}
