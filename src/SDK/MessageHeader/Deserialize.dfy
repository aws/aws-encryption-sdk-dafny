include "Definitions.dfy"
include "Utils.dfy"
include "Validity.dfy"
include "../Materials.dfy"

include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

/*
 * The message header deserialization
 *
 * The message header is deserialized from a uint8 stream.
 * When encountering an error, we stop and return it immediately, leaving the remaining inputs on the stream
 */
module MessageHeader.Deserialize {
  import Msg = Definitions
  import V = Validity
  import Utils

  import AlgorithmSuite
  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import Materials

  method DeserializeVersion(rd: Streams.StringReader) returns (ret: Result<Msg.Version>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
  {
    var version :- rd.ReadExact(1);
    if version[0] == Msg.VERSION_1 {
      return Success(version[0]);
    } else {
      return Failure("Deserialization Error: Version not supported.");
    }
  }

  method DeserializeType(rd: Streams.StringReader) returns (ret: Result<Msg.Type>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
  {
    var typ :- rd.ReadExact(1);
    if typ[0] == Msg.TYPE_CUSTOMER_AED {
      return Success(typ[0]);
    } else {
      return Failure("Deserialization Error: Type not supported.");
    }
  }

  method DeserializeAlgorithmSuiteID(rd: Streams.StringReader) returns (ret: Result<AlgorithmSuite.ID>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(algorithmSuiteID) => V.ValidAlgorithmID(algorithmSuiteID)
      case Failure(_) => true
  {
    var algorithmSuiteID :- rd.ReadUInt16();
    if algorithmSuiteID in AlgorithmSuite.validIDs {
      return Success(algorithmSuiteID as AlgorithmSuite.ID);
    } else {
      return Failure("Deserialization Error: Algorithm suite not supported.");
    }
  }

  method DeserializeMsgID(rd: Streams.StringReader) returns (ret: Result<Msg.MessageID>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(msgID) => V.ValidMessageID(msgID)
      case Failure(_) => true
  {
    var msgID: seq<uint8> :- rd.ReadExact(Msg.MESSAGE_ID_LEN);
    return Success(msgID);
  }

  method DeserializeUTF8(rd: Streams.StringReader, n: nat) returns (ret: Result<seq<uint8>>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(bytes) =>
        && |bytes| == n
        && UTF8.ValidUTF8Seq(bytes)
      case Failure(_) => true
  {
    var bytes :- rd.ReadExact(n);
    if UTF8.ValidUTF8Seq(bytes) {
      return Success(bytes);
    } else {
      return Failure("Deserialization Error: Not a valid UTF8 string.");
    }
  }

  method DeserializeAAD(rd: Streams.StringReader) returns (ret: Result<Materials.EncryptionContext>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(aad) => V.ValidAAD(aad)
      case Failure(_) => true
  {
    reveal V.ValidAAD();

    var aadLength :- rd.ReadUInt16();
    if aadLength == 0 {
      return Success([]);
    } else if aadLength < 2 {
      return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
    }
    var totalBytesRead := 0;

    var kvPairsCount :- rd.ReadUInt16();
    totalBytesRead := totalBytesRead + 2;
    if kvPairsCount == 0 {
      return Failure("Deserialization Error: Key value pairs count is 0.");
    }

    // TODO: declare this array, make kvPairs a ghost, maintain invariant that sequence is a prefix of the array:
    // var kvPairsArray: array<(seq<uint8>, seq<uint8>)> := new [kvPairsCount];
    var kvPairs: seq<(seq<uint8>, seq<uint8>)> := [];
    var i := 0;
    while i < kvPairsCount
      invariant rd.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant totalBytesRead == 2 + V.KVPairsLength(kvPairs, 0, i as nat) <= aadLength as nat
      invariant V.ValidAAD(kvPairs)
    {
      var keyLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;

      var key :- DeserializeUTF8(rd, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;

      var valueLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      // check that we're not exceeding the stated AAD length
      if aadLength as nat < totalBytesRead + valueLength as nat {
        return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
      }

      var value :- DeserializeUTF8(rd, valueLength as nat);
      totalBytesRead := totalBytesRead + |value|;

      // We want to keep entries sorted by key. We don't insist that the entries be sorted
      // already, but we do insist there are no duplicate keys.
      var opt, insertionPoint := Utils.InsertNewEntry(kvPairs, key, value);
      match opt {
        case Some(kvPairs_) =>
          V.KVPairsLengthInsert(kvPairs, insertionPoint, key, value);
          kvPairs := kvPairs_;
        case None =>
          return Failure("Deserialization Error: Duplicate key.");
      }

      i := i + 1;
    }
    if aadLength as nat != totalBytesRead {
      return Failure("Deserialization Error: Bytes actually read differs from bytes supposed to be read.");
    }
    return Success(kvPairs);
  }

  method DeserializeEncryptedDataKeys(rd: Streams.StringReader) returns (ret: Result<Msg.EncryptedDataKeys>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(edks) => V.ValidEncryptedDataKeys(edks)
      case Failure(_) => true
  {
    reveal V.ValidEncryptedDataKeys();

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
      var keyProviderID := ByteSeqToString(str);

      // Key provider info
      var keyProviderInfoLength :- rd.ReadUInt16();
      var keyProviderInfo :- rd.ReadExact(keyProviderInfoLength as nat);

      // Encrypted data key
      var edkLength :- rd.ReadUInt16();
      var edk :- rd.ReadExact(edkLength as nat);

      edkEntries := edkEntries + [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)];
      i := i + 1;
    }

    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(rd: Streams.StringReader) returns (ret: Result<Msg.ContentType>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
  {
    var bytes :- rd.ReadExact(1);
    match Msg.UInt8ToContentType(bytes[0])
    case None =>
      return Failure("Deserialization Error: Content type not supported.");
    case Some(contentType) =>
      return Success(contentType);
  }

  method DeserializeReserved(rd: Streams.StringReader) returns (ret: Result<Msg.Reserved>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
  {
    var reserved :- rd.ReadExact(4);
    if reserved[0] == reserved[1] == reserved[2] == reserved[3] == 0 {
      return Success(reserved[..]);
    } else {
      return Failure("Deserialization Error: Reserved fields must be 0.");
    }
  }

  method DeserializeIVLength(rd: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<uint8>)
    requires rd.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    ensures rd.Valid()
    modifies rd
    ensures match ret
      case Success(ivLength) => V.ValidIVLength(ivLength, algorithmSuiteID)
      case Failure(_) => true
  {
    var ivLength :- rd.ReadExact(1);
    if ivLength[0] == AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen {
      return Success(ivLength[0]);
    } else {
      return Failure("Deserialization Error: Incorrect IV length.");
    }
  }

  method DeserializeFrameLength(rd: Streams.StringReader, contentType: Msg.ContentType) returns (ret: Result<uint32>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(frameLength) => V.ValidFrameLength(frameLength, contentType)
      case Failure(_) => true
  {
    var frameLength :- rd.ReadExact(4);
    if contentType.NonFramed? && SeqToUInt32(frameLength) == 0 {
      return Success(SeqToUInt32(frameLength));
    } else {
      return Failure("Deserialization Error: Frame length must be 0 when content type is non-framed.");
    }
  }

  /**
  * Reads raw header data from the input stream and populates the header with all of the information about the
  * message.
  */
  method DeserializeHeaderBody(rd: Streams.StringReader) returns (ret: Result<Msg.HeaderBody>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(hb) => V.ValidHeaderBody(hb)
      case Failure(_) => true
  {
    reveal V.ValidHeaderBody();

    var version :- DeserializeVersion(rd);
    var typ :- DeserializeType(rd);
    var algorithmSuiteID :- DeserializeAlgorithmSuiteID(rd);
    var messageID :- DeserializeMsgID(rd);
    var aad :- DeserializeAAD(rd);
    var encryptedDataKeys :- DeserializeEncryptedDataKeys(rd);
    var contentType :- DeserializeContentType(rd);
    var reserved :- DeserializeReserved(rd);
    var ivLength :- DeserializeIVLength(rd, algorithmSuiteID);
    var frameLength :- DeserializeFrameLength(rd, contentType);
    
    var hb := Msg.HeaderBody(
      version,
      typ,
      algorithmSuiteID,
      messageID,
      aad,
      encryptedDataKeys,
      contentType,
      reserved,
      ivLength,
      frameLength);
    return Success(hb);
  }

  method DeserializeHeaderAuthentication(rd: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<Msg.HeaderAuthentication>)
    requires rd.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies rd
    ensures rd.Valid()
    ensures match ret
      case Success(ha) => V.ValidHeaderAuthentication(ha, algorithmSuiteID)
      case Failure(_) => true
  {
    var params := AlgorithmSuite.Suite[algorithmSuiteID].params;
    var iv :- rd.ReadExact(params.ivLen as nat);
    var authenticationTag :- rd.ReadExact(params.tagLen as nat);
    return Success(Msg.HeaderAuthentication(iv[..], authenticationTag[..]));
  }
}
