include "Definitions.dfy"
include "Utils.dfy"
include "Validity.dfy"

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
  import opened Definitions
  import opened Validity
  import Utils

  import AlgorithmSuite
  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8

  /*
   * Message header-specific
   */

  method DeserializeVersion(is: Streams.StringReader) returns (ret: Result<T_Version>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var version :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if version[0] == 0x01 {
      return Success(version[0] as T_Version);
    } else {
      return Failure("Deserialization Error: Version not supported.");
    }
  }

  method DeserializeType(is: Streams.StringReader) returns (ret: Result<T_Type>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var typ :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if typ[0] == 0x80 {
      return Success(typ[0] as T_Type);
    } else {
      return Failure("Deserialization Error: Type not supported.");
    }
  }

  method DeserializeAlgorithmSuiteID(is: Streams.StringReader) returns (ret: Result<AlgorithmSuite.ID>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(algorithmSuiteID) => ValidAlgorithmID(algorithmSuiteID)
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

  // TODO:
  predicate method IsValidMsgID (candidateID: array<uint8>)
    requires candidateID.Length == 16
    ensures ValidMessageId(candidateID[..])
  {
    true
  }

  method DeserializeMsgID(is: Streams.StringReader) returns (ret: Result<T_MessageID>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(msgId) => ValidMessageId(msgId)
      case Failure(_) => true
  {
    var msgId :- Utils.ReadFixedLengthFromStreamOrFail(is, 16);
    if IsValidMsgID(msgId) {
      return Success(msgId[..]);
    } else {
      return Failure("Deserialization Error: Not a valid Message ID.");
    }
  }

  method DeserializeUTF8(is: Streams.StringReader, n: nat) returns (ret: Result<array<uint8>>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(bytes) =>
        && bytes.Length == n
        && UTF8.ValidUTF8(bytes)
        && fresh(bytes)
      case Failure(_) => true
  {
    var bytes :- Utils.ReadFixedLengthFromStreamOrFail(is, n);
    if UTF8.ValidUTF8(bytes) {
      return Success(bytes);
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

  // TODO: Probably this should be factored out into EncCtx at some point
  method DeserializeAAD(is: Streams.StringReader) returns (ret: Result<T_AAD>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(aad) => ValidAAD(aad)
      case Failure(_) => true
  {
    reveal ValidAAD();

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
      invariant totalBytesRead == 2 + KVPairsLength(kvPairs, 0, i) <= aadLength as nat
      invariant ValidAAD(kvPairs)
    {
      bytes :- DeserializeUnrestricted(is, 2);
      var keyLength := ArrayToUInt16(bytes);
      totalBytesRead := totalBytesRead + bytes.Length;

      bytes :- DeserializeUTF8(is, keyLength as nat);
      UTF8.ValidUTF8ArraySeq(bytes);
      var key := bytes[..];
      totalBytesRead := totalBytesRead + bytes.Length;

      bytes :- DeserializeUnrestricted(is, 2);
      var valueLength := ArrayToUInt16(bytes);
      totalBytesRead := totalBytesRead + bytes.Length;
      // check that we're not exceeding the stated AAD length
      if aadLength as nat < totalBytesRead + valueLength as nat {
        return Failure("Deserialization Error: The number of bytes in encryption context exceeds the given length.");
      }

      bytes :- DeserializeUTF8(is, valueLength as nat);
      UTF8.ValidUTF8ArraySeq(bytes);
      var value := bytes[..];
      totalBytesRead := totalBytesRead + bytes.Length;

      // check for sortedness by key
      if i != 0 && !LexCmpSeqs(kvPairs[i - 1].0, key, UInt8Less) {
        return Failure("Deserialization Error: Key-value pairs must be sorted by key.");
      }

      KVPairsLengthExtend(kvPairs, key, value);
      kvPairs := kvPairs + [(key, value)];
      i := i + 1;
    }
    if aadLength as nat != totalBytesRead {
      return Failure("Deserialization Error: Bytes actually read differs from bytes supposed to be read.");
    }
    return Success(kvPairs);
  }

  // TODO: Probably this should be factored out into EDK at some point
  method DeserializeEncryptedDataKeys(is: Streams.StringReader) returns (ret: Result<T_EncryptedDataKeys>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(edks) => ValidEncryptedDataKeys(edks)
      case Failure(_) => true
  {
    reveal ValidEncryptedDataKeys();

    var bytes :- DeserializeUnrestricted(is, 2);
    var edkCount := ArrayToUInt16(bytes);
    if edkCount == 0 {
      return Failure("Deserialization Error: Encrypted data key count must be > 0.");
    }

    var edkEntries: seq<EDKEntry> := [];
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
      bytes :- DeserializeUTF8(is, keyProviderIDLength as nat);
      keyProviderID := ByteSeqToString(bytes[..]);

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

    var edks := EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(is: Streams.StringReader) returns (ret: Result<T_ContentType>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
  {
    var contentType :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if contentType[0] == 0x01 {
      return Success(NonFramed);
    } else if contentType[0] == 0x02 {
      return Success(Framed);
    } else {
      return Failure("Deserialization Error: Content type not supported.");
    }
  }

  method DeserializeReserved(is: Streams.StringReader) returns (ret: Result<T_Reserved>)
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

  method DeserializeIVLength(is: Streams.StringReader, algSuiteId: AlgorithmSuite.ID) returns (ret: Result<uint8>)
    requires is.Valid()
    requires algSuiteId in AlgorithmSuite.Suite.Keys
    ensures is.Valid()
    modifies is
    ensures match ret
      case Success(ivLength) => ValidIVLength(ivLength, algSuiteId)
      case Failure(_) => true
  {
    var ivLength :- Utils.ReadFixedLengthFromStreamOrFail(is, 1);
    if ivLength[0] == AlgorithmSuite.Suite[algSuiteId].params.ivLen {
      return Success(ivLength[0]);
    } else {
      return Failure("Deserialization Error: Incorrect IV length.");
    }
  }

  method DeserializeFrameLength(is: Streams.StringReader, contentType: T_ContentType) returns (ret: Result<uint32>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(frameLength) => ValidFrameLength(frameLength, contentType)
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
  method DeserializeHeaderBody(is: Streams.StringReader) returns (ret: Result<HeaderBody>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(hb) => ValidHeaderBody(hb)
      case Failure(_) => true
  {
    reveal ValidHeaderBody();

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
    
    var hb := HeaderBody(
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

  method DeserializeAuthenticationTag(is: Streams.StringReader, tagLength: nat, ghost iv: array<uint8>) returns (ret: Result<array<uint8>>)
    requires is.Valid()
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(authenticationTag) => ValidAuthenticationTag(authenticationTag, tagLength, iv)
      case Failure(_) => true
  {
    ret := Utils.ReadFixedLengthFromStreamOrFail(is, tagLength);
  }

  method DeserializeAuthenticationHeader(is: Streams.StringReader, body: HeaderBody) returns (ret: Result<HeaderAuthentication>)
    requires is.Valid()
    requires ValidHeaderBody(body)
    requires body.algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies is
    ensures is.Valid()
    ensures match ret
      case Success(headerAuthentication) =>
        && ValidHeaderAuthentication(headerAuthentication, body.algorithmSuiteID)
        && ValidHeaderBody(body)
      case Failure(_) => true
  {
    var iv :- DeserializeUnrestricted(is, body.ivLength as nat);
    var authenticationTag :- DeserializeAuthenticationTag(is, AlgorithmSuite.Suite[body.algorithmSuiteID].params.tagLen as nat, iv);
    return Success(HeaderAuthentication(iv, authenticationTag));
  }
}
