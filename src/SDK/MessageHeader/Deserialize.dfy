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

  method DeserializeVersion(is: Streams.StringReader) returns (ret: Result<Msg.Version>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var version :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if version[0] == Msg.VERSION_1 {
      return Success(version[0]);
    } else {
      return Failure("Deserialization Error: Version not supported.");
    }
  }

  method DeserializeType(is: Streams.StringReader) returns (ret: Result<Msg.Type>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var typ :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if typ[0] == Msg.TYPE_CUSTOMER_AED {
      return Success(typ[0]);
    } else {
      return Failure("Deserialization Error: Type not supported.");
    }
  }

  method DeserializeAlgorithmSuiteID(is: Streams.StringReader) returns (ret: Result<AlgorithmSuite.ID>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(algorithmSuiteID) => V.ValidAlgorithmID(algorithmSuiteID)
      case Failure(_) => true
  {
    var algorithmSuiteID :- Utils.ReadFixedLengthFromStreamOrFail(is, 2);
    var asid := ArrayToUInt16(algorithmSuiteID);
    if asid in AlgorithmSuite.validIDs {
      return Success(asid as AlgorithmSuite.ID);
    } else {
      return Failure("Deserialization Error: Algorithm suite not supported.");
    }
  }

  method DeserializeMsgID(is: Streams.StringReader) returns (ret: Result<Msg.MessageID>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(msgID) => V.ValidMessageID(msgID)
      case Failure(_) => true
  {
    var id :- Utils.ReadFixedLengthFromStreamOrFail(is, 16);
    var msgID := id[..];
    return Success(id[..]);
  }

  method DeserializeUTF8(is: Streams.StringReader, n: nat) returns (ret: Result<seq<uint8>>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(str) =>
        && |str| == n
        && UTF8.ValidUTF8Seq(str)
      case Failure(_) => true
  {
    var bytes :- Utils.ReadFixedLengthFromStreamOrFail(is, n);
    var str := bytes[..];
    if UTF8.ValidUTF8Seq(str) {
      return Success(str);
    } else {
      return Failure("Deserialization Error: Not a valid UTF8 string.");
    }
  }

  method DeserializeUnrestricted(is: Streams.StringReader, n: nat) returns (ret: Result<array<uint8>>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(bytes) =>
        && bytes.Length == n
        && fresh(bytes)
      case Failure(_) => true
  {
    ret := Utils.ReadFixedLengthFromStreamOrFail(is, n);
  }

  // TODO: Probably this should be factored out into Materials.EncryptionContext at some point
  method DeserializeAAD(is: Streams.StringReader) returns (ret: Result<Materials.EncryptionContext>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(aad) => V.ValidAAD(aad)
      case Failure(_) => true
  {
    reveal V.ValidAAD();

    var bytes :- DeserializeUnrestricted(is, 2);
    var aadLength := ArrayToUInt16(bytes);
    if aadLength == 0 {
      return Success([]);
    } else if aadLength < 2 {
      return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
    }
    var totalBytesRead := 0;

    bytes :- DeserializeUnrestricted(is, 2);
    var kvPairsCount := ArrayToUInt16(bytes) as nat;
    totalBytesRead := totalBytesRead + bytes.Length;
    if kvPairsCount == 0 {
      return Failure("Deserialization Error: Key value pairs count is 0.");
    }

    // TODO: declare this array, make kvPairs a ghost, maintain invariant that sequence is a prefix of the array:
    // var kvPairsArray: array<(seq<uint8>, seq<uint8>)> := new [kvPairsCount];
    var kvPairs: seq<(seq<uint8>, seq<uint8>)> := [];
    var i: nat := 0;
    while i < kvPairsCount
      invariant is.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant totalBytesRead == 2 + V.KVPairsLength(kvPairs, 0, i) <= aadLength as nat
      invariant V.ValidAAD(kvPairs)
    {
      bytes :- DeserializeUnrestricted(is, 2);
      var keyLength := ArrayToUInt16(bytes);
      totalBytesRead := totalBytesRead + bytes.Length;

      var key :- DeserializeUTF8(is, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;

      bytes :- DeserializeUnrestricted(is, 2);
      var valueLength := ArrayToUInt16(bytes);
      totalBytesRead := totalBytesRead + bytes.Length;
      // check that we're not exceeding the stated AAD length
      if aadLength as nat < totalBytesRead + valueLength as nat {
        return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
      }

      var value :- DeserializeUTF8(is, valueLength as nat);
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

  // TODO: Probably this should be factored out into EDK at some point
  method DeserializeEncryptedDataKeys(is: Streams.StringReader) returns (ret: Result<Msg.EncryptedDataKeys>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(edks) => V.ValidEncryptedDataKeys(edks)
      case Failure(_) => true
  {
    reveal V.ValidEncryptedDataKeys();

    var bytes :- DeserializeUnrestricted(is, 2);
    var edkCount := ArrayToUInt16(bytes);
    if edkCount == 0 {
      return Failure("Deserialization Error: Encrypted data key count is 0.");
    }

    var edkEntries: seq<Materials.EncryptedDataKey> := [];
    var i := 0;
    while i < edkCount
      invariant is.Valid()
      invariant i <= edkCount
      invariant |edkEntries| == i as int
      invariant forall i :: 0 <= i < |edkEntries| ==> edkEntries[i].Valid()
    {
      // Key provider ID
      var keyProviderIDLength: uint16;
      bytes :- DeserializeUnrestricted(is, 2);
      keyProviderIDLength := ArrayToUInt16(bytes);

      var keyProviderID: string;
      var str :- DeserializeUTF8(is, keyProviderIDLength as nat);
      keyProviderID := ByteSeqToString(str);

      // Key provider info
      var keyProviderInfoLength: uint16;
      bytes :- DeserializeUnrestricted(is, 2);
      keyProviderInfoLength := ArrayToUInt16(bytes);

      var keyProviderInfo: seq<uint8>;
      bytes :- DeserializeUnrestricted(is, keyProviderInfoLength as nat);
      keyProviderInfo := bytes[..];

      // Encrypted data key
      var edkLength: uint16;
      bytes :- DeserializeUnrestricted(is, 2);
      edkLength := ArrayToUInt16(bytes);

      var edk: seq<uint8>;
      bytes :- DeserializeUnrestricted(is, edkLength as nat);
      edk := bytes[..];

      edkEntries := edkEntries + [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)];
      i := i + 1;
    }

    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(is: Streams.StringReader) returns (ret: Result<Msg.ContentType>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var bytes :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    match Msg.UInt8ToContentType(bytes[0])
    case None =>
      return Failure("Deserialization Error: Content type not supported.");
    case Some(contentType) =>
      return Success(contentType);
  }

  method DeserializeReserved(is: Streams.StringReader) returns (ret: Result<Msg.Reserved>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var reserved :- Utils.ReadFixedLengthFromStreamOrFail(is, 4);
    if reserved[0] == reserved[1] == reserved[2] == reserved[3] == 0 {
      return Success(reserved[..]);
    } else {
      return Failure("Deserialization Error: Reserved fields must be 0.");
    }
  }

  method DeserializeIVLength(is: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<uint8>)
    requires is.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    ensures is.Valid()
    modifies is
    ensures match ret
      case Success(ivLength) => V.ValidIVLength(ivLength, algorithmSuiteID)
      case Failure(_) => true
  {
    var ivLength :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if ivLength[0] == AlgorithmSuite.Suite[algorithmSuiteID].params.ivLen {
      return Success(ivLength[0]);
    } else {
      return Failure("Deserialization Error: Incorrect IV length.");
    }
  }

  method DeserializeFrameLength(is: Streams.StringReader, contentType: Msg.ContentType) returns (ret: Result<uint32>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(frameLength) => V.ValidFrameLength(frameLength, contentType)
      case Failure(_) => true
  {
    var frameLength :- Utils.ReadFixedLengthFromStreamOrFail(is, 4);
    if contentType.NonFramed? && ArrayToUInt32(frameLength) == 0 {
      return Success(ArrayToUInt32(frameLength));
    } else {
      return Failure("Deserialization Error: Frame length must be 0 when content type is non-framed.");
    }
  }

  /**
  * Reads raw header data from the input stream and populates the header with all of the information about the
  * message.
  */
  method DeserializeHeaderBody(is: Streams.StringReader) returns (ret: Result<Msg.HeaderBody>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(hb) => V.ValidHeaderBody(hb)
      case Failure(_) => true
  {
    reveal V.ValidHeaderBody();

    var version :- DeserializeVersion(is);
    var typ :- DeserializeType(is);
    var algorithmSuiteID :- DeserializeAlgorithmSuiteID(is);
    var messageID :- DeserializeMsgID(is);
    var aad :- DeserializeAAD(is);
    var encryptedDataKeys :- DeserializeEncryptedDataKeys(is);
    var contentType :- DeserializeContentType(is);
    var reserved :- DeserializeReserved(is);
    var ivLength :- DeserializeIVLength(is, algorithmSuiteID);
    var frameLength :- DeserializeFrameLength(is, contentType);
    
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

  method DeserializeHeaderAuthentication(is: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<Msg.HeaderAuthentication>)
    requires is.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(ha) => V.ValidHeaderAuthentication(ha, algorithmSuiteID)
      case Failure(_) => true
  {
    var params := AlgorithmSuite.Suite[algorithmSuiteID].params;
    var iv :- DeserializeUnrestricted(is, params.ivLen as nat);
    var authenticationTag :- DeserializeUnrestricted(is, params.tagLen as nat);
    return Success(Msg.HeaderAuthentication(iv[..], authenticationTag[..]));
  }
}
