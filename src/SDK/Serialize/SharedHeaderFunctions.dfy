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
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<MessageFormatVersion>)
    ensures CorrectlyRead(bytes, res, WriteMessageFormatVersion)
  {
    var rawVersion :- SerializeFunctions.Read(bytes, 1);

    var version :- MessageFormatVersion.Get(rawVersion.thing).MapFailure(e => Error(e));
    Success(Data(version, rawVersion.tail))
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
    messageId: MessageID
  ):
    (ret: seq<uint8>)
  {
    messageId
  }

  function method ReadMessageId(
    bytes: ReadableBytes
  )
    :(res: ReadBinaryCorrect<MessageID>)
    ensures CorrectlyRead(bytes, res, WriteMessageId)
  {
    SerializeFunctions.Read(bytes, MESSAGE_ID_LEN)
  }

  function method WriteContentType(
    contentType: ContentType
  ):
    (ret: seq<uint8>)
  {
    [contentType.Serialize()]
  }

  function method ReadContentType(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<ContentType>)
    ensures CorrectlyRead(bytes, res, WriteContentType)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, 1);
    var contentType :- ContentType.Get(raw[0]).MapFailure(e => Error(e));
    Success(Data(contentType, tail))
  }
}
