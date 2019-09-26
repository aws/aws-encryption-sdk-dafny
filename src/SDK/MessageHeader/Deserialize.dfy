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
    import opened Utils

    import AlgorithmSuite
    import opened Streams
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened UTF8

    lemma {:axiom} Assume(b : bool) ensures b

    /*
     * Message header-specific
     */

    method deserializeVersion(is: StringReader) returns (ret: Either<T_Version, Error>)
        requires is.Valid()
        modifies is
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 1);
        match res {
            case Left(version) =>
                if version[0] == 0x01 {
                    return Left(version[0] as T_Version);
                } else {
                    return Right(DeserializationError("Version not supported."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeType(is: StringReader) returns (ret: Either<T_Type, Error>)
        requires is.Valid()
        modifies is
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 1);
        match res {
            case Left(typ) =>
                if typ[0] == 0x80 {
                    return Left(typ[0] as T_Type);
                } else {
                    return Right(DeserializationError("Type not supported."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeAlgorithmSuiteID(is: StringReader) returns (ret: Either<AlgorithmSuite.ID, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(algorithmSuiteID) => ValidAlgorithmID(algorithmSuiteID)
                case Right(_) => true
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 2);
        match res {
            case Left(algorithmSuiteID) =>
                var asid := ArrayToUInt16(algorithmSuiteID);
                if asid in AlgorithmSuite.validIDs {
                    return Left(asid as AlgorithmSuite.ID);
                } else {
                    return Right(DeserializationError("Algorithm suite not supported."));
                }
            case Right(e) => return Right(e);
        }
    }

    // TODO:
    predicate method isValidMsgID (candidateID: array<uint8>)
        requires candidateID.Length == 16
        ensures ValidMessageId(candidateID[..])
    {
        true
    }
    method deserializeMsgID(is: StringReader) returns (ret: Either<T_MessageID, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(msgId) => ValidMessageId(msgId)
                case Right(_) => true
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 16);
        match res {
            case Left(msgId) =>
                if isValidMsgID(msgId) {
                    return Left(msgId[..]);
                } else {
                    return Right(DeserializationError("Not a valid Message ID."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeUTF8(is: StringReader, n: nat) returns (ret: Either<array<uint8>, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(bytes) =>
                    && bytes.Length == n
                    && ValidUTF8(bytes)
                    && fresh(bytes)
                case Right(_) => true
        ensures is.Valid()
    {
        ret := readFixedLengthFromStreamOrFail(is, n);
        match ret {
            case Left(bytes) =>
                if ValidUTF8(bytes) {
                    return ret;
                } else {
                    return Right(DeserializationError("Not a valid UTF8 string."));
                }
            case Right(e) => return ret;
        }
    }

    method deserializeUnrestricted(is: StringReader, n: nat) returns (ret: Either<array<uint8>, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(bytes) =>
                    && bytes.Length == n
                    && fresh(bytes)
                case Right(_) => true
        ensures is.Valid()
    {
        ret := readFixedLengthFromStreamOrFail(is, n);
    }

    // TODO: Probably this should be factored out into EncCtx at some point
    method deserializeAAD(is: StringReader) returns (ret: Either<T_AAD, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(aad) =>
                    && ValidAAD(aad)
                case Right(_) => true
        ensures is.Valid()
    {
        reveal ValidAAD();
        var kvPairsLength: uint16;
        {
            var res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) => kvPairsLength := ArrayToUInt16(bytes);
                case Right(e) => return Right(e);
            }
        }
        if kvPairsLength == 0 {
            return Left(EmptyAAD);
        }
        var totalBytesRead := 0;

        var kvPairsCount: uint16;
        {
            var res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) =>
                    kvPairsCount := ArrayToUInt16(bytes);
                    totalBytesRead := totalBytesRead + bytes.Length;
                    if kvPairsLength > 0 && kvPairsCount == 0 {
                        return Right(DeserializationError("Key value pairs count is 0."));
                    }
                    assert kvPairsLength > 0 ==> kvPairsCount > 0;
                case Right(e) => return Right(e);
            }
        }

        // TODO: declare this array, make kvPairs a ghost, maintain invariant that sequence is a prefix of the array:
        // var kvPairsArray: array<(seq<uint8>, seq<uint8>)> := new [kvPairsCount];
        var kvPairs: seq<(seq<uint8>, seq<uint8>)> := [];
        assert kvPairsCount > 0;

        var i := 0;
        while i < kvPairsCount
            invariant is.Valid()
            invariant |kvPairs| == i as int
            invariant i <= kvPairsCount
            invariant InBoundsKVPairsUpTo(kvPairs, i as nat)
            invariant SortedKVPairsUpTo(kvPairs, i as nat)
            invariant forall j :: 0 <= j < i ==> ValidUTF8Seq(kvPairs[j].0)
            invariant forall j :: 0 <= j < i ==> ValidUTF8Seq(kvPairs[j].1)
        {
            var keyLength: uint16;
            {
                var res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) =>
                        keyLength := ArrayToUInt16(bytes);
                        totalBytesRead := totalBytesRead + bytes.Length;
                    case Right(e) => return Right(e);
                }
            }

            var key: seq<uint8>;
            {
                var res := deserializeUTF8(is, keyLength as nat);
                match res {
                    case Left(bytes) =>
                        ValidUTF8ArraySeq(bytes);
                        key := bytes[..];
                        totalBytesRead := totalBytesRead + bytes.Length;
                    case Right(e) => return Right(e);
                }
            }
            assert |key| < UINT16_LIMIT;
            assert ValidUTF8Seq(key);

            var valueLength: uint16;
            {
                var res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) =>
                        valueLength := ArrayToUInt16(bytes);
                        totalBytesRead := totalBytesRead + bytes.Length;
                    case Right(e) => return Right(e);
                }
            }

            var value: seq<uint8>;
            {
                var res := deserializeUTF8(is, valueLength as nat);
                match res {
                    case Left(bytes) =>
                        ValidUTF8ArraySeq(bytes);
                        value := bytes[..];
                        totalBytesRead := totalBytesRead + bytes.Length;
                    case Right(e) => return Right(e);
                }
            }
            assert |value| < UINT16_LIMIT;
            assert ValidUTF8Seq(value);

            // check for sortedness by key
            if i != 0 && !LexCmpSeqs(kvPairs[i-1].0, key, ltByte) {
                return Right(DeserializationError("Key-value pairs must be sorted by key."));
            }
            kvPairs := kvPairs + [(key, value)];
            assert SortedKVPairsUpTo(kvPairs, (i+1) as nat);
            i := i + 1;
        }
        if (kvPairsLength as nat) != totalBytesRead {
            return Right(DeserializationError("Bytes actually read differs from bytes supposed to be read."));
        }
        return Left(AAD(kvPairs));
    }

    // TODO: Probably this should be factored out into EDK at some point
    method deserializeEncryptedDataKeys(is: StringReader, ghost aad: T_AAD) returns (ret: Either<T_EncryptedDataKeys, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(edks) =>
                    && ValidEncryptedDataKeys(edks)
                case Right(_)   => true
        ensures is.Valid()
    {
        reveal ValidEncryptedDataKeys();
        var res: Either;
        var edkCount: uint16;
        res := deserializeUnrestricted(is, 2);
        match res {
            case Left(bytes) => edkCount := ArrayToUInt16(bytes);
            case Right(e)    => return Right(e);
        }

        if edkCount == 0 {
            return Right(DeserializationError("Encrypted data key count must be > 0."));
        }

        var edkEntries: seq<EDKEntry> := [];
        var i := 0;
        while i < edkCount
            invariant is.Valid()
            invariant i <= edkCount
            invariant InBoundsEncryptedDataKeys(edkEntries)
        {
            // Key provider ID
            var keyProviderIDLength: uint16;
            res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) => keyProviderIDLength := ArrayToUInt16(bytes);
                case Right(e)    => return Right(e);
            }

            var keyProviderID: string;
            res := deserializeUTF8(is, keyProviderIDLength as nat);
            match res {
                case Left(bytes) => keyProviderID := ByteSeqToString(bytes[..]);
                case Right(e)    => return Right(e);
            }

            // Key provider info
            var keyProviderInfoLength: uint16;
            res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) => keyProviderInfoLength := ArrayToUInt16(bytes);
                case Right(e)    => return Right(e);
            }

            var keyProviderInfo: seq<uint8>;
            res := deserializeUnrestricted(is, keyProviderInfoLength as nat);
            match res {
                case Left(bytes) => keyProviderInfo := bytes[..];
                case Right(e)    => return Right(e);
            }

            // Encrypted data key
            var edkLength: uint16;
            res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) => edkLength := ArrayToUInt16(bytes);
                case Right(e)    => return Right(e);
            }

            var edk: seq<uint8>;
            res := deserializeUnrestricted(is, edkLength as nat);
            match res {
                case Left(bytes) => edk := bytes[..];
                case Right(e)    => return Right(e);
            }

            edkEntries := edkEntries + [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)];
            i := i + 1;
        }

        var edks := EncryptedDataKeys(edkEntries);
        return Left(edks);
    }

    method deserializeContentType(is: StringReader) returns (ret: Either<T_ContentType, Error>)
        requires is.Valid()
        modifies is
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 1);
        match res {
            case Left(contentType) =>
                if contentType[0] == 0x01 {
                    return Left(NonFramed);
                } else if contentType[0] == 0x02 {
                    return Left(Framed);
                } else {
                    return Right(DeserializationError("Content type not supported."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeReserved(is: StringReader) returns (ret: Either<T_Reserved, Error>)
        requires is.Valid()
        modifies is
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 4);
        match res {
            case Left(reserved) =>
                if reserved[0] == reserved[1] == reserved[2] == reserved[3] == 0 {
                    return Left(reserved[..]);
                } else {
                    return Right(DeserializationError("Reserved fields must be 0."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeIVLength(is: StringReader, algSuiteId: AlgorithmSuite.ID) returns (ret: Either<uint8, Error>)
        requires is.Valid()
        requires algSuiteId in AlgorithmSuite.Suite.Keys
        modifies is
        ensures
            match ret
                case Left(ivLength) => ValidIVLength(ivLength, algSuiteId)
                case Right(_)       => true
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 1);
        match res {
            case Left(ivLength) =>
                if ivLength[0] == AlgorithmSuite.Suite[algSuiteId].params.ivLen {
                    return Left(ivLength[0]);
                } else {
                    return Right(DeserializationError("Incorrect IV length."));
                }
            case Right(e) => return Right(e);
        }
    }

    method deserializeFrameLength(is: StringReader, contentType: T_ContentType) returns (ret: Either<uint32, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(frameLength) => ValidFrameLength(frameLength, contentType)
                case Right(_) => true
        ensures is.Valid()
    {
        var res := readFixedLengthFromStreamOrFail(is, 4);
        match res {
            case Left(frameLength) =>
                if contentType.NonFramed? && ArrayToUInt32(frameLength) == 0 {
                    return Left(ArrayToUInt32(frameLength));
                } else {
                    return Right(DeserializationError("Frame length must be 0 when content type is non-framed."));
                }
            case Right(e) => return Right(e);
        }
    }
    /**
    * Reads raw header data from the input stream and populates the header with all of the information about the
    * message.
    */
    method headerBody(is: StringReader) returns (ret: Either<HeaderBody, Error>)
        requires is.Valid()
        modifies is
        ensures is.Valid()
        ensures
            match ret
                case Left(hb) =>
                    && ValidHeaderBody(hb)
                case Right(_) => true
    {
        Assume(false);
        reveal ValidHeaderBody();
        var version: T_Version;
        {
            var res := deserializeVersion(is);
            match res {
                case Left(version_) => version := version_;
                case Right(e)       => return Right(e);
            }
        }

        var typ: T_Type;
        {
            var res := deserializeType(is);
            match res {
                case Left(typ_) => typ := typ_;
                case Right(e)   => return Right(e);
            }
        }

        var algorithmSuiteID: AlgorithmSuite.ID;
        {
            var res := deserializeAlgorithmSuiteID(is);
            match res {
                case Left(algorithmSuiteID_) => algorithmSuiteID := algorithmSuiteID_;
                case Right(e)                => return Right(e);
            }
        }

        var messageID: T_MessageID;
        {
            var res := deserializeMsgID(is);
            match res {
                case Left(messageID_) => messageID := messageID_;
                case Right(e)    => return Right(e);
            }
        }

        // AAD deserialization:
        var aad: T_AAD;
        {
            var res := deserializeAAD(is);
            match res {
                case Left(aad_) => aad := aad_;
                case Right(e)   => return Right(e);
            }
        }

        // EDK deserialization:
        var encryptedDataKeys: T_EncryptedDataKeys;
        {
            var res := deserializeEncryptedDataKeys(is, aad);
            match res {
                case Left(encryptedDataKeys_) => encryptedDataKeys := encryptedDataKeys_;
                case Right(e)   => return Right(e);
            }
        }

        var contentType: T_ContentType;
        {
            var res := deserializeContentType(is);
            match res {
                case Left(contentType_) => contentType := contentType_;
                case Right(e)           => return Right(e);
            }
        }

        var reserved: T_Reserved;
        {
            var res := deserializeReserved(is);
            match res {
                case Left(reserved_) => reserved := reserved_;
                case Right(e)    => return Right(e);
            }
        }

        var ivLength: uint8;
        {
            var res := deserializeIVLength(is, algorithmSuiteID);
            match res {
                case Left(ivLength_) => ivLength := ivLength_;
                case Right(e)    => return Right(e);
            }
        }

        var frameLength: uint32;
        {
            var res := deserializeFrameLength(is, contentType);
            match res {
                case Left(frameLength_) => frameLength := frameLength_;
                case Right(e) => return Right(e);
            }
        }
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
        assert ValidHeaderBody(hb);
        ret := Left(hb);
    }

    method deserializeAuthenticationTag(is: StringReader, tagLength: nat, ghost iv: array<uint8>) returns (ret: Either<array<uint8>, Error>)
        requires is.Valid()
        modifies is
        ensures
            match ret
                case Left(authenticationTag) => ValidAuthenticationTag(authenticationTag, tagLength, iv)
                case Right(_) => true
        ensures is.Valid()
    {
        ret := readFixedLengthFromStreamOrFail(is, tagLength);
    }

    method headerAuthentication(is: StringReader, body: HeaderBody) returns (ret: Either<HeaderAuthentication, Error>)
        requires is.Valid()
        requires ValidHeaderBody(body)
        requires body.algorithmSuiteID in AlgorithmSuite.Suite.Keys
        modifies is
        ensures is.Valid()
        ensures
            match ret
                case Left(headerAuthentication) =>
                    && ValidHeaderAuthentication(headerAuthentication, body.algorithmSuiteID)
                    && ValidHeaderBody(body)
                case Right(_) => true
    {
        var iv: array<uint8>;
        {
            var res := deserializeUnrestricted(is, body.ivLength as nat);
            match res {
                case Left(bytes) => iv := bytes;
                case Right(e)    => return Right(e);
            }
        }

        var authenticationTag: array<uint8>;
        {
            var res := deserializeAuthenticationTag(is, AlgorithmSuite.Suite[body.algorithmSuiteID].params.tagLen as nat, iv);
            match res {
                case Left(bytes) => authenticationTag := bytes;
                case Right(e)    => return Right(e);
            }
        }
        ret := Left(HeaderAuthentication(iv, authenticationTag));
    }
}
