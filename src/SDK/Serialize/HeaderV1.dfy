// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "Header.dfy"
include "EncryptionContext.dfy"
include "EncryptedDataKeys.dfy"

module HeaderV1 {
  import Aws.Crypto
  import Seq
  import Header
  import MaterialProviders.Client
  import opened EncryptedDataKeys
  import opened EncryptionContext2
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  type V1HeaderBody = h: Header.HeaderBody
  | h.HeaderBodyV1?
  witness *

  const VERSION_1: seq<uint8> := [0x01];
  type Version = s: seq<uint8>
  | s == VERSION_1
  witness VERSION_1

  const RESERVED_BYTES: seq<uint8> := [0x00, 0x00, 0x00, 0x00];
  type ReservedBytes = s: seq<uint8>
  | s == RESERVED_BYTES
  witness RESERVED_BYTES

  function method WriteHeaderBodyV1(
    body: V1HeaderBody
  ):
    (ret: seq<uint8>)
  {

    var suiteId := GetAlgorithmSuiteId(body.esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);

    WriteV1Version(VERSION_1)
    + WriteV1MessageType(body.messageType)
    + WriteESDKSuiteId(body.esdkSuiteId)
    + WriteMessageId(body.messageId)
    + WriteAADSection(body.encryptionContext)
    + WriteEncryptedDataKeys(body.encryptedDataKeys)
    + WriteContentType(body.contentType)
    + WriteV1ReservedBytes(RESERVED_BYTES)
    + WriteV1HeaderIvLength(suite.encrypt.ivLength)
    + UInt32ToSeq(body.frameLength)
  }

  function method ReadHeaderBodyV1(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<V1HeaderBody>)
    ensures
      || CorrectlyRead(bytes, res, WriteHeaderBodyV1)
      // This is to handle the edge case in empty AAD see: `ReadAADSection`
      || (
        var headerBytesToAADStart := 20; 
        var aadStartPosition := bytes.start+headerBytesToAADStart;
        && res.Success?
        && aadStartPosition+4 < |bytes.data|
        && bytes.data[aadStartPosition..aadStartPosition+4] == [0,2,0,0]
        ==>
          && CorrectlyRead(bytes, res, WriteExpandedAADSectionHeaderBodyV1))

  {
    var version :- ReadV1Version(bytes);

    var messageType :- ReadV1MessageType(version.tail);

    var esdkSuiteId :- ReadESDKSuiteId(messageType.tail);

    var messageId :- ReadMessageId(esdkSuiteId.tail);

    var encryptionContext :- EncryptionContext2.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail);

    var contentType :- ReadContentType(encryptedDataKeys.tail);

    var reservedBytes :- ReadV1ReservedBytes(contentType.tail);

    var suiteId := GetAlgorithmSuiteId(esdkSuiteId.thing);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    var headerIvLength :- ReadV1HeaderIvLength(
      reservedBytes.tail,
      suite
    );

    var frameLength :- ReadUInt32(headerIvLength.tail);

    var body:V1HeaderBody := Header.HeaderBodyV1(
      messageType := messageType.thing,
      esdkSuiteId := esdkSuiteId.thing,
      messageId := messageId.thing,
      encryptionContext := encryptionContext.thing,
      encryptedDataKeys := encryptedDataKeys.thing,
      contentType := contentType.thing,
      headerIvLength := headerIvLength.thing as nat,
      frameLength := frameLength.thing
    );

    Success(Data(body, frameLength.tail))
  }

  function method WriteV1Version(
    version: Version
  ):
    (ret: seq<uint8>)
  {
    version
  }

  function method ReadV1Version(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<Version>)
    ensures CorrectlyRead(bytes, res, WriteV1Version)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, |VERSION_1|);
    :- Need(raw == VERSION_1, Error("Incorrect message version."));
    var version: Version := raw;
    Success(Data(version, tail))
  }

  function method WriteV1MessageType(
    messageType: Header.MessageType
  ):
    (ret: seq<uint8>)
  {
    [messageType.Serialize()]
  }

  function method ReadV1MessageType(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<Header.MessageType>)
    ensures CorrectlyRead(bytes, res, WriteV1MessageType)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, 1);
    var messageType :- Header.MessageType.Get(raw[0]).MapFailure(e => Error(e));
    Success(Data(messageType, tail))
  }

  function method WriteESDKSuiteId(
    esdkSuiteId: ESDKAlgorithmSuiteId
  ):
    (ret: seq<uint8>)
  {
    UInt16ToSeq(esdkSuiteId)
  }

  function method ReadESDKSuiteId(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<ESDKAlgorithmSuiteId>)
    ensures CorrectlyRead(bytes, res, WriteESDKSuiteId)
  {
    var Data(esdkSuiteId, tail) :- ReadUInt16(bytes);
    :- Need(esdkSuiteId in VALID_IDS, Error("Algorithm suite ID not supported."));
    Success(Data(esdkSuiteId, tail))
  }

  function method WriteMessageId(
    messageId: Header.MessageID
  ):
    (ret: seq<uint8>)
  {
    messageId
  }

  function method ReadMessageId(
    bytes: ReadableBytes
  )
    :(res: ReadBinaryCorrect<Header.MessageID>)
    ensures CorrectlyRead(bytes, res, WriteMessageId)
  {
    SerializeFunctions.Read(bytes, Header.MESSAGE_ID_LEN)
  }

  function method WriteContentType(
    contentType: Header.ContentType
  ):
    (ret: seq<uint8>)
  {
    [contentType.Serialize()]
  }

  function method ReadContentType(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<Header.ContentType>)
    ensures CorrectlyRead(bytes, res, WriteContentType)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, 1);
    var contentType :- Header.ContentType.Get(raw[0]).MapFailure(e => Error(e));
    Success(Data(contentType, tail))
  }

  function method WriteV1ReservedBytes(
    reservedBytes: ReservedBytes
  ):
    (ret: seq<uint8>)
  {
    reservedBytes
  }

  function method ReadV1ReservedBytes(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<ReservedBytes>)
    ensures CorrectlyRead(bytes, res, WriteV1ReservedBytes)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, |RESERVED_BYTES|);
    :- Need(raw == RESERVED_BYTES, Error("Incorrect reserved bytes."));
    var reservedBytes: ReservedBytes := raw;
    Success(Data(reservedBytes, tail))
  }

  function method WriteV1HeaderIvLength(
    ivLength: uint8
  ):
    (ret: seq<uint8>)
  {
    [ivLength]
  }

  function method ReadV1HeaderIvLength(
    bytes: ReadableBytes,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: ReadCorrect<uint8>)
    ensures CorrectlyRead(bytes, res, WriteV1HeaderIvLength)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, 1);
    :- Need(raw[0] == suite.encrypt.ivLength, Error("HeaderIv Length does not match Algorithm Suite."));
    Success(Data(raw[0], tail))
  }

  // This is *not* a function method,
  // because it is *only* used for correctness.
  // This represents the sub-optimal encoding of AAD
  // where empty AAD is encoded with an extra 2 bytes.
  function WriteExpandedAADSectionHeaderBodyV1(
    body: V1HeaderBody
  ):
    (ret: seq<uint8>)
  {

    var suiteId := GetAlgorithmSuiteId(body.esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);

    WriteV1Version(VERSION_1)
    + WriteV1MessageType(body.messageType)
    + WriteESDKSuiteId(body.esdkSuiteId)
    + WriteMessageId(body.messageId)
    + WriteExpandedAADSection(body.encryptionContext)
    + WriteEncryptedDataKeys(body.encryptedDataKeys)
    + WriteContentType(body.contentType)
    + WriteV1ReservedBytes(RESERVED_BYTES)
    + WriteV1HeaderIvLength(suite.encrypt.ivLength)
    + UInt32ToSeq(body.frameLength)
  }

}