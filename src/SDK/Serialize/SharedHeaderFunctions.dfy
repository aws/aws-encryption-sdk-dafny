// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../AwsCryptographicMaterialProviders/Client.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"
include "./SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "EncryptionContext.dfy"
include "HeaderTypes.dfy"

module SharedHeaderFunctions {
  import Aws.Crypto
  import Seq
  import MaterialProviders.Client
  import EncryptionContext
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions
  import opened HeaderTypes

  function method WriteMessageFormatVersion(
    version: MessageFormatVersion
  )
    :(ret : seq<uint8>)
  {
    Write(version.Serialize())
  }

  function method ReadMessageFormatVersion(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<MessageFormatVersion>)
    ensures CorrectlyRead(buffer, res, WriteMessageFormatVersion)
  {
    var rawVersion :- SerializeFunctions.Read(buffer, 1);

    var version :- MessageFormatVersion.Get(rawVersion.data).MapFailure(e => Error(e));
    Success(SuccessfulRead(version, rawVersion.tail))
  }

  function method WriteESDKSuiteId(
    esdkSuiteId: ESDKAlgorithmSuiteId
  ):
    (ret: seq<uint8>)
  {
    UInt16ToSeq(esdkSuiteId)
  }

  function method ReadESDKSuiteId(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<ESDKAlgorithmSuiteId>)
    ensures CorrectlyRead(buffer, res, WriteESDKSuiteId)
  {
    var SuccessfulRead(esdkSuiteId, tail) :- ReadUInt16(buffer);
    :- Need(esdkSuiteId in VALID_IDS, Error("Algorithm suite ID not supported."));
    Success(SuccessfulRead(esdkSuiteId, tail))
  }

  function method WriteMessageIdV1(
    messageId: MessageId
  ):
    (ret: seq<uint8>)
  {
    messageId
  }

  function method ReadMessageIdV1(
    buffer: ReadableBuffer
  )
    :(res: ReadBinaryCorrect<MessageId>)
    ensures CorrectlyRead(buffer, res, WriteMessageIdV1)
  {
    var messageIdRead :- SerializeFunctions.Read(buffer, MESSAGE_ID_LEN_V1);
    var messageId: MessageId := messageIdRead.data;

    Success(SuccessfulRead(messageId, messageIdRead.tail))
  }

  function method WriteMessageIdV2(
    messageId: MessageId
  ):
    (ret: seq<uint8>)
  {
    messageId
  }

  function method ReadMessageIdV2(
    buffer: ReadableBuffer
  )
    :(res: ReadBinaryCorrect<MessageId>)
    ensures CorrectlyRead(buffer, res, WriteMessageIdV1)
  {
    var messageIdRead :- SerializeFunctions.Read(buffer, MESSAGE_ID_LEN_V2);
    var messageId: MessageId := messageIdRead.data;

    Success(SuccessfulRead(messageId, messageIdRead.tail))
  }

  function method WriteContentType(
    contentType: ContentType
  ):
    (ret: seq<uint8>)
  {
    [contentType.Serialize()]
  }

  function method ReadContentType(
    buffer: ReadableBuffer
  )
    :(res: ReadCorrect<ContentType>)
    ensures CorrectlyRead(buffer, res, WriteContentType)
  {
    var SuccessfulRead(raw, tail) :- SerializeFunctions.Read(buffer, 1);
    var contentType :- ContentType.Get(raw[0]).MapFailure(e => Error(e));
    Success(SuccessfulRead(contentType, tail))
  }
}
