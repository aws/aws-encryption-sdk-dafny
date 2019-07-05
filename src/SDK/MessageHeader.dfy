include "../SDK/AlgorithmSuite.dfy"
include "../Util/Streams.dfy"
include "../Util/StandardLibrary.dfy"
include "../Util/UTF8.dfy"

module MessageHeader {
    import AlgorithmSuite
    import opened Streams
    import opened StandardLibrary
    import opened UTF8

    /*
     * Header body type definition
     */
    type T_Version         = x | x == 0x01 /*Version 1.0*/ witness 0x01
    type T_Type            = x | x == 0x80 /*Customer Authenticated Encrypted Data*/ witness 0x80
    type T_MessageID       = x: seq<byte> | |x| == 16 witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    type T_Reserved        = x: seq<byte> | x == [0,0,0,0] witness [0,0,0,0]
    datatype T_ContentType = NonFramed | Framed
    type EncCtx            = array<(array<byte>, array<byte>)>
    datatype T_AAD         = AAD(length: uint16, kvPairs: EncCtx) | EmptyAAD

    datatype EDKEntry      = EDKEntry(keyProviderId: array<byte>, keyProviderInfo: array<byte>, encDataKey: array<byte>)
    datatype T_EncryptedDataKeys
                           = EncryptedDataKeys(count: uint16, entries: array<EDKEntry>) | EmptyEncryptedDataKeys

    datatype HeaderBody    = HeaderBody(
                                version: T_Version, 
                                typ: T_Type,
                                algorithmSuiteID: AlgorithmSuite.ID,
                                messageID: T_MessageID,
                                aad: T_AAD,
                                encryptedDataKeys: T_EncryptedDataKeys,
                                contentType: T_ContentType,
                                reserved: T_Reserved,
                                ivLength: uint8,
                                frameLength: uint32)

    /*
     * Header authentication type definition
     */
    
    datatype HeaderAuthentication = HeaderAuthentication(iv: array<byte>, authenticationTag: array<byte>)

    /*
     * Utils
     */
    method readFixedLengthFromStreamOrFail(is: StringReader, n: nat) returns (ret: Result<array<byte>>)
        requires is.valid()
        modifies is
        ensures
            match ret
                case Left(bytes) => n == bytes.Length
                case Right(_)    => true
        ensures is.valid()
    {
        var bytes := new byte[n];
        var out: Either<nat,Error>;
        out := is.Read(bytes, 0, n);
        match out {
            case Left(bytesRead) =>
                if bytesRead != n {
                    return Right(IOError("Not enough bytes left on stream."));
                } else {
                    return Left(bytes);
                }
            case Right(e) => return Right(e);
        }
    }

    predicate sortedUpTo(a: array<(array<byte>, array<byte>)>, n: nat)
        requires n <= a.Length
        reads a
        reads set i | 0 <= i < n :: a[i].0
    {
        forall j :: 0 < j < n ==> lexCmpArrays(a[j-1].0, a[j].0, ltByte)
    }

    predicate sorted(a: array<(array<byte>, array<byte>)>)
        reads a
        reads set i | 0 <= i < a.Length :: a[i].0
    {
        sortedUpTo(a, a.Length)
    }

    /*
     * Definition of the message header, i.e., the header body and the header authentication
     */
    class Header {
        var body: HeaderBody
        var auth: HeaderAuthentication

        static method deserializeVersion(is: StringReader) returns (ret: Result<T_Version>)
            requires is.valid()
            modifies is
            ensures is.valid()
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

        static method deserializeType(is: StringReader) returns (ret: Result<T_Type>)
            requires is.valid()
            modifies is
            ensures is.valid()
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

        static method deserializeAlgorithmSuiteID(is: StringReader) returns (ret: Result<AlgorithmSuite.ID>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(algorithmSuiteID) => ValidAlgorithmID(algorithmSuiteID)
                    case Right(_) => true
            ensures is.valid()
        {
            var res := readFixedLengthFromStreamOrFail(is, 1);
            match res {
                case Left(algorithmSuiteID) =>
                    if (algorithmSuiteID[0] as AlgorithmSuite.ID) in AlgorithmSuite.Suite.Keys {
                        return Left(algorithmSuiteID[0] as AlgorithmSuite.ID);
                    } else {
                        return Right(DeserializationError("Algorithm suite not supported."));
                    }
                case Right(e) => return Right(e);
            }
        }

        static predicate method isValidMsgID (candidateID: array<byte>)
            requires candidateID.Length == 16
        {
            // TODO:
            true
        }
        static method deserializeMsgID(is: StringReader) returns (ret: Result<T_MessageID>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(msgId) => ValidMessageId(msgId)
                    case Right(_) => true
            ensures is.valid()
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

        static method deserializeUTF8(is: StringReader, n: nat) returns (ret: Result<array<byte>>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(bytes) =>
                        && bytes.Length == n
                        && ValidUTF8(bytes, 0)
                    case Right(_) => true
            ensures is.valid()
        {
            ret := readFixedLengthFromStreamOrFail(is, n);
            match ret {
                case Left(bytes) =>
                    if ValidUTF8(bytes, 0) {
                        return ret;
                    } else {
                        return Right(DeserializationError("Not a valid UTF8 string."));
                    }
                case Right(e) => return ret;
            }
        }

        static method deserializeUnrestricted(is: StringReader, n: nat) returns (ret: Result<array<byte>>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(bytes) => bytes.Length == n
                    case Right(_) => true
            ensures is.valid()
        {
            ret := readFixedLengthFromStreamOrFail(is, n);
        }

        function encCtxToSeqs(kvPairs: array<(array<byte>, array<byte>)>, i: nat): seq<(seq<byte>, seq<byte>)>
            decreases kvPairs.Length - i
            reads kvPairs
            reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].0
            reads set i | 0 <= i < kvPairs.Length :: kvPairs[i].1
        {
            if i < kvPairs.Length
            then [(kvPairs[i].0[..], kvPairs[i].1[..])] + encCtxToSeqs(kvPairs, i + 1)
            else []
        }

        // TODO: Probably this should be factored out into EncCtx at some point
        static method deserializeAAD(is: StringReader) returns (ret: Result<T_AAD>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(aad) => ValidAAD(aad)
                    case Right(_) => true
            ensures is.valid()
        {
            var kvPairsLength: uint16;
            {
                var res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) => kvPairsLength := deser_uint16_from_array(bytes);
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
                        kvPairsCount := deser_uint16_from_array(bytes);
                        totalBytesRead := totalBytesRead + bytes.Length;
                        if kvPairsLength > 0 && kvPairsCount == 0 {
                            return Right(DeserializationError("Key value pairs count is 0."));
                        }
                        assert kvPairsLength > 0 ==> kvPairsCount > 0;
                    case Right(e) => return Right(e);
                }
            }

            var kvPairs: EncCtx := new [kvPairsCount];
            assert kvPairs.Length > 0;
            assert kvPairsCount == kvPairs.Length as uint16;

            var i := 0;
            while i < kvPairsCount
                invariant is.valid()
                invariant i <= kvPairsCount
                invariant sortedUpTo(kvPairs, i as nat)
                invariant forall j :: 0 <= j < i ==> ValidUTF8(kvPairs[j].0, 0)
                invariant forall j :: 0 <= j < i ==> ValidUTF8(kvPairs[j].1, 0)
            {
                var keyLength: uint16;
                {
                    var res := deserializeUnrestricted(is, 2);
                    match res {
                        case Left(bytes) =>
                            keyLength := deser_uint16_from_array(bytes);
                            totalBytesRead := totalBytesRead + bytes.Length;
                        case Right(e) => return Right(e);
                    }
                }

                var key := new byte[keyLength];
                {
                    var res := deserializeUTF8(is, keyLength as nat);
                    match res {
                        case Left(bytes) =>
                            key := bytes;
                            totalBytesRead := totalBytesRead + bytes.Length;
                        case Right(e) => return Right(e);
                    }
                }

                var valueLength: uint16;
                {
                    var res := deserializeUnrestricted(is, 2);
                    match res {
                        case Left(bytes) =>
                            valueLength := deser_uint16_from_array(bytes);
                            totalBytesRead := totalBytesRead + bytes.Length;
                        case Right(e) => return Right(e);
                    }
                }

                var value := new byte[valueLength];
                {
                    var res := deserializeUTF8(is, valueLength as nat);
                    match res {
                        case Left(bytes) =>
                            value := bytes;
                            totalBytesRead := totalBytesRead + bytes.Length;
                        case Right(e) => return Right(e);
                    }
                }
                
                // check for sortedness by key
                if i > 0 {
                    if lexCmpArrays(kvPairs[i-1].0, key, ltByte) {
                        kvPairs[i] := (key, value);
                    } else {
                        return Right(DeserializationError("Key-value pairs must be sorted by key."));
                    }
                } else {
                    assert i == 0;
                    kvPairs[i] := (key, value);
                }
                assert sortedUpTo(kvPairs, (i+1) as nat);
                i := i + 1;
            }
            if (kvPairsLength as nat) != totalBytesRead {
                return Right(DeserializationError("Bytes actually read differs from bytes supposed to be read."));
            }
            return Left(AAD(kvPairsLength, kvPairs));
        }

        // TODO: Probably this should be factored out into EDK at some point
        static method deserializeEncryptedDataKeys(is: StringReader, ghost aad: T_AAD) returns (ret: Result<T_EncryptedDataKeys>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(edks) => ValidEncryptedDataKeys(edks)
                    case Right(_)   => true
            ensures is.valid()
        {
            var res: Result;
            var edkCount: uint16;
            res := deserializeUnrestricted(is, 2);
            match res {
                case Left(bytes) => edkCount := deser_uint16_from_array(bytes);
                case Right(e)    => return Right(e);
            }

            if edkCount == 0 {
                return Left(EmptyEncryptedDataKeys);
            }

            var edks: array<EDKEntry> := new [edkCount];

            var i := 0;
            while i < edkCount
                invariant is.valid()
            {
                // Key provider ID
                var keyProviderIDLength: uint16;
                res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) => keyProviderIDLength := deser_uint16_from_array(bytes);
                    case Right(e)    => return Right(e);
                }

                var keyProviderID := new byte[keyProviderIDLength];
                res := deserializeUTF8(is, keyProviderIDLength as nat);
                match res {
                    case Left(bytes) => keyProviderID := bytes;
                    case Right(e)    => return Right(e);
                }

                // Key provider info
                var keyProviderInfoLength: uint16;
                res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) => keyProviderInfoLength := deser_uint16_from_array(bytes);
                    case Right(e)    => return Right(e);
                }
                
                var keyProviderInfo := new byte[keyProviderInfoLength];
                res := deserializeUTF8(is, keyProviderInfoLength as nat);
                match res {
                    case Left(bytes) => keyProviderInfo := bytes;
                    case Right(e)    => return Right(e);
                }

                // Encrypted data key
                var edkLength: uint16;
                res := deserializeUnrestricted(is, 2);
                match res {
                    case Left(bytes) => edkLength := deser_uint16_from_array(bytes);
                    case Right(e)    => return Right(e);
                }
                
                var edk := new byte[edkLength];
                res := deserializeUTF8(is, edkLength as nat);
                match res {
                    case Left(bytes) => edk := bytes;
                    case Right(e)    => return Right(e);
                }
                
                var edkEntry := EDKEntry(keyProviderID, keyProviderInfo, edk);
                edks[i] := edkEntry;
                i := i + 1;
            }

            return Left(EncryptedDataKeys(edkCount, edks));
        }

        static method deserializeContentType(is: StringReader) returns (ret: Result<T_ContentType>)
            requires is.valid()
            modifies is
            ensures is.valid()
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

        static method deserializeReserved(is: StringReader) returns (ret: Result<T_Reserved>)
            requires is.valid()
            modifies is
            ensures is.valid()
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

        static method deserializeIVLength(is: StringReader, algSuiteId: AlgorithmSuite.ID) returns (ret: Result<uint8>)
            requires is.valid()
            requires algSuiteId in AlgorithmSuite.Suite.Keys
            modifies is
            ensures
                match ret
                    case Left(ivLength) => ValidIVLength(ivLength, algSuiteId)
                    case Right(_)       => true
            ensures is.valid()
        {
            var res := readFixedLengthFromStreamOrFail(is, 1);
            match res {
                case Left(ivLength) =>
                    if ivLength[0] == AlgorithmSuite.Suite[algSuiteId].params.iv_len {
                        return Left(ivLength[0]);
                    } else {
                        return Right(DeserializationError("Incorrect IV length."));
                    }
                case Right(e) => return Right(e);
            }
        }

        static method deserializeFrameLength(is: StringReader, contentType: T_ContentType) returns (ret: Result<uint32>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(frameLength) => ValidFrameLength(frameLength, contentType)
                    case Right(_) => true
            ensures is.valid()
        {
            var res := readFixedLengthFromStreamOrFail(is, 4);
            match res {
                case Left(frameLength) =>
                    if contentType.NonFramed? && deser_uint32_from_array(frameLength) == 0 {
                        return Left(deser_uint32_from_array(frameLength));
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
        static method deserializeHeaderBody(is: StringReader) returns (ret: Result<HeaderBody>)
            requires is.valid()
            modifies is
            ensures is.valid()
            ensures
                match ret
                    case Left(hb) => Valid(hb)
                    case Right(_) => true
        {
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

            ret := Left(
                    HeaderBody(
                        version,
                        typ,
                        algorithmSuiteID,
                        messageID,
                        aad,
                        encryptedDataKeys,
                        contentType,
                        reserved,
                        ivLength,
                        frameLength));
        }

        static method deserializeAuthenticationTag(is: StringReader, tagLength: nat, ghost iv: array<byte>) returns (ret: Result<array<byte>>)
            requires is.valid()
            modifies is
            ensures
                match ret
                    case Left(authenticationTag) => ValidAuthenticationTag(authenticationTag, tagLength, iv)
                    case Right(_) => true
            ensures is.valid()
        {
            ret := readFixedLengthFromStreamOrFail(is, tagLength);
        }

        static method deserializeHeaderAuthentication(is: StringReader, body: HeaderBody) returns (ret: Result<HeaderAuthentication>)
            requires is.valid()
            requires body.algorithmSuiteID in AlgorithmSuite.Suite.Keys
            modifies is
            ensures is.valid()
            ensures
                match ret
                    case Left(headerAuthentication) => ValidHeaderAuthentication(headerAuthentication, body.algorithmSuiteID)
                    case Right(_) => true
        {
            var iv: array<byte>;
            {
                var res := deserializeUnrestricted(is, body.ivLength as nat);
                match res {
                    case Left(bytes) => iv := bytes;
                    case Right(e)    => return Right(e);
                }
            }
            
            var authenticationTag: array<byte>;
            {
                var res := deserializeAuthenticationTag(is, AlgorithmSuite.Suite[body.algorithmSuiteID].params.tag_len as nat, iv);
                match res {
                    case Left(bytes) => authenticationTag := bytes;
                    case Right(e)    => return Right(e);
                }
            }
            ret := Left(HeaderAuthentication(iv, authenticationTag));
        }
    }

    /*
     * Validity of the message header
     * The validity depends on predicates and on the types of the fields
     */
    predicate Valid(hb: HeaderBody)
        reads 
            match hb.aad 
                case AAD(_, kvPairs) =>
                    (set i | 0 <= i < kvPairs.Length :: kvPairs[i].0) + (set i | 0 <= i < kvPairs.Length :: kvPairs[i].1) + {kvPairs}
                case EmptyAAD() => {}
    {
        && ValidAlgorithmID(hb.algorithmSuiteID)
        && ValidMessageId(hb.messageID)
        && ValidAAD(hb.aad)
        && ValidEncryptedDataKeys(hb.encryptedDataKeys)
        && ValidIVLength(hb.ivLength, hb.algorithmSuiteID)
        && ValidFrameLength(hb.frameLength, hb.contentType)
    }

    // TODO: move axiomatization somewhere central
    predicate {:axiom} uniquelyIdentifiesMessage(id: T_MessageID)      { true }
    predicate {:axiom} weaklyBindsHeaderToHeaderBody(id: T_MessageID)  { true }
    predicate {:axiom} enablesSecureReuse(id: T_MessageID)             { true }
    predicate {:axiom} protectsAgainstAccidentalReuse(id: T_MessageID) { true }
    predicate {:axiom} protectsAgainstWearingOut(id: T_MessageID)      { true }
    predicate ValidMessageId(id: T_MessageID)
    {
        && uniquelyIdentifiesMessage(id)
        && weaklyBindsHeaderToHeaderBody(id)
        && enablesSecureReuse(id)
        && protectsAgainstAccidentalReuse(id)
        && protectsAgainstWearingOut(id)
    }
    predicate ValidAlgorithmID(algorithmSuiteID: AlgorithmSuite.ID)
    {
         algorithmSuiteID in AlgorithmSuite.Suite.Keys
    }
    predicate ValidAAD(aad: T_AAD)
        reads 
            match aad 
                case AAD(_, kvPairs) =>
                    (set i | 0 <= i < kvPairs.Length :: kvPairs[i].0) + (set i | 0 <= i < kvPairs.Length :: kvPairs[i].1) + {kvPairs}
                case EmptyAAD() => {}
    {
        match aad {
            case AAD(kvPairsLength, kvPairs) =>
                && kvPairsLength > 0
                && forall i :: 0 <= i < kvPairs.Length ==> ValidUTF8(kvPairs[i].0, 0) && ValidUTF8(kvPairs[i].1, 0)
                && sorted(kvPairs)
            case EmptyAAD() => true
        }
    }
    predicate ValidEncryptedDataKeys(EncryptedDataKeys: T_EncryptedDataKeys)
    {
        EncryptedDataKeys.EncryptedDataKeys? ==>
            EncryptedDataKeys.count > 0
            // TODO: well-formedness of EDK
            /*
            Key Provider ID
            The key provider identifier. The value of this field indicates the provider of the encrypted data key. See Key Provider for details on supported key providers.

            Key Provider Information
            The key provider information. The key provider for this encrypted data key determines what this field contains.

            Encrypted Data Key
            The encrypted data key. It is the data key encrypted by the key provider.
            */
    }
    predicate ValidIVLength(ivLength: uint8, algorithmSuiteID: AlgorithmSuite.ID)
    {
        algorithmSuiteID in AlgorithmSuite.Suite.Keys && AlgorithmSuite.Suite[algorithmSuiteID].params.iv_len == ivLength
    }
    predicate ValidFrameLength(frameLength: uint32, contentType: T_ContentType)
    {
        match contentType {
            case NonFramed => frameLength == 0
            case Framed => true
        }
    }

    /*
     * Validity of the message header authentication
     */
    predicate ValidAuthenticationTag(authenticationTag: array<byte>, tagLength: nat, iv: array<byte>)
    {
        true
        // TODO:
        // The algorithm suite specified by the Algorithm Suite ID field determines how the value of this field is calculated, and uses this value to authenticate the contents of the header during decryption.
    }
    predicate ValidHeaderAuthentication(ha: HeaderAuthentication, algorithmSuiteID: AlgorithmSuite.ID)
        requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    {
        ValidAuthenticationTag(ha.authenticationTag, AlgorithmSuite.Suite[algorithmSuiteID].params.tag_len as nat, ha.iv)
    }
}