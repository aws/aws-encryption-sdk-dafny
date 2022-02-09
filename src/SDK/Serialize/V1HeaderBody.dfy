// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "HeaderTypes.dfy"
include "SharedHeaderFunctions.dfy"
include "EncryptionContext.dfy"
include "EncryptedDataKeys.dfy"

module V1HeaderBody {
  import Aws.Crypto
  import Seq
  import HeaderTypes
  import SharedHeaderFunctions
  import MaterialProviders.Client
  import opened EncryptedDataKeys
  import opened EncryptionContext
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  type V1HeaderBody = h: HeaderTypes.HeaderBody
  | h.V1HeaderBody?
  witness *

  const RESERVED_BYTES: seq<uint8> := [0x00, 0x00, 0x00, 0x00];
  type ReservedBytes = s: seq<uint8>
  | s == RESERVED_BYTES
  witness RESERVED_BYTES

  function method WriteV1HeaderBody(
    body: V1HeaderBody
  )
    :(ret: seq<uint8>)
  {

    var suiteId := GetAlgorithmSuiteId(body.esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);

    SharedHeaderFunctions.WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V1)
    + WriteV1MessageType(body.messageType)
    + SharedHeaderFunctions.WriteESDKSuiteId(body.esdkSuiteId)
    + SharedHeaderFunctions.WriteMessageId(body.messageId)
    + WriteAADSection(body.encryptionContext)
    + WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    + SharedHeaderFunctions.WriteContentType(body.contentType)
    + WriteV1ReservedBytes(RESERVED_BYTES)
    + WriteV1HeaderIvLength(suite.encrypt.ivLength)
    + UInt32ToSeq(body.frameLength)
  }

  function method ReadV1HeaderBody(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<V1HeaderBody>)
    ensures CorrectlyReadV1HeaderBody(buffer, res)
  {
    var version :- SharedHeaderFunctions.ReadMessageFormatVersion(buffer);
    :- Need(version.data.V1?, Error("Message version must be version 1."));

    var messageType :- ReadV1MessageType(version.tail);

    var esdkSuiteId :- SharedHeaderFunctions.ReadESDKSuiteId(messageType.tail);
    var suiteId := GetAlgorithmSuiteId(esdkSuiteId.data);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    :- Need(suite.commitment.None?, Error("Algorithm suite must not support commitment."));

    var messageId :- SharedHeaderFunctions.ReadMessageIdV1(esdkSuiteId.tail);

    var encryptionContext :- EncryptionContext.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail);

    var contentType :- SharedHeaderFunctions.ReadContentType(encryptedDataKeys.tail);

    var reservedBytes :- ReadV1ReservedBytes(contentType.tail);

    var headerIvLength :- ReadV1HeaderIvLength(
      reservedBytes.tail,
      suite
    );

    var frameLength :- ReadUInt32(headerIvLength.tail);

    var body:V1HeaderBody := HeaderTypes.V1HeaderBody(
      messageType := messageType.data,
      esdkSuiteId := esdkSuiteId.data,
      messageId := messageId.data,
      encryptionContext := encryptionContext.data,
      encryptedDataKeys := encryptedDataKeys.data,
      contentType := contentType.data,
      headerIvLength := headerIvLength.data as nat,
      frameLength := frameLength.data
    );

    Success(SuccessfulRead(body, frameLength.tail))
  }

  // TODO: This needs to be proven
  predicate CorrectlyReadV1HeaderBody(
    buffer: ReadableBuffer,
    res: ReadCorrect<V1HeaderBody>
  )
  {
    && res.Success? ==> CorrectlyReadRange(buffer, res.value.tail)
    && (
      || (
          !IsV1ExpandedAADSection(buffer)
        ==>
          && CorrectlyRead(buffer, res, WriteV1HeaderBody))
      // This is to handle the edge case in empty AAD see: `ReadAADSection`
      || (
          IsV1ExpandedAADSection(buffer)
        ==>
          && CorrectlyRead(buffer, res, WriteV1ExpandedAADSectionHeaderBody)))
  }

  predicate IsV1ExpandedAADSection(
    buffer: ReadableBuffer
  )
  {
    var headerBytesToAADStart := 20; 
    var aadStartPosition := buffer.start+headerBytesToAADStart;
    && aadStartPosition+4 < |buffer.bytes|
    && buffer.bytes[aadStartPosition..aadStartPosition+4] == [0,2,0,0]
  }

  function method WriteV1MessageType(
    messageType: HeaderTypes.MessageType
  ):
    (ret: seq<uint8>)
  {
    [messageType.Serialize()]
  }

  function method ReadV1MessageType(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<HeaderTypes.MessageType>)
    ensures CorrectlyRead(buffer, res, WriteV1MessageType)
  {
    var SuccessfulRead(raw, tail) :- SerializeFunctions.Read(buffer, 1);
    var messageType :- HeaderTypes.MessageType.Get(raw[0]).MapFailure(e => Error(e));
    Success(SuccessfulRead(messageType, tail))
  }

  function method WriteV1ReservedBytes(
    reservedBytes: ReservedBytes
  ):
    (ret: seq<uint8>)
  {
    reservedBytes
  }

  function method ReadV1ReservedBytes(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<ReservedBytes>)
    ensures CorrectlyRead(buffer, res, WriteV1ReservedBytes)
  {
    var SuccessfulRead(raw, tail) :- SerializeFunctions.Read(buffer, |RESERVED_BYTES|);
    :- Need(raw == RESERVED_BYTES, Error("Incorrect reserved bytes."));
    var reservedBytes: ReservedBytes := raw;
    Success(SuccessfulRead(reservedBytes, tail))
  }

  function method WriteV1HeaderIvLength(
    ivLength: uint8
  )
    :(ret: seq<uint8>)
  {
    [ivLength]
  }

  function method ReadV1HeaderIvLength(
    buffer: ReadableBuffer,
    suite: Client.AlgorithmSuites.AlgorithmSuite
  )
    :(res: ReadCorrect<uint8>)
    ensures CorrectlyRead(buffer, res, WriteV1HeaderIvLength)
  {
    var SuccessfulRead(raw, tail) :- SerializeFunctions.Read(buffer, 1);
    :- Need(raw[0] == suite.encrypt.ivLength, Error("HeaderIv Length does not match Algorithm Suite."));
    Success(SuccessfulRead(raw[0], tail))
  }

  // This is *not* a function method,
  // because it is *only* used for correctness.
  // This represents the sub-optimal encoding of AAD
  // where empty AAD is encoded with an extra 2 bytes.
  function WriteV1ExpandedAADSectionHeaderBody(
    body: V1HeaderBody
  )
    :(ret: seq<uint8>)
  {

    var suiteId := GetAlgorithmSuiteId(body.esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);

    SharedHeaderFunctions.WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V1)
    + WriteV1MessageType(body.messageType)
    + SharedHeaderFunctions.WriteESDKSuiteId(body.esdkSuiteId)
    + SharedHeaderFunctions.WriteMessageId(body.messageId)
    + WriteExpandedAADSection(body.encryptionContext)
    + WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    + SharedHeaderFunctions.WriteContentType(body.contentType)
    + WriteV1ReservedBytes(RESERVED_BYTES)
    + WriteV1HeaderIvLength(suite.encrypt.ivLength)
    + UInt32ToSeq(body.frameLength)
  }

}
