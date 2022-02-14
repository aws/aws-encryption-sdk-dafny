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

module V2HeaderBody {
  import Aws.Crypto
  import Seq
  import HeaderTypes
  import opened SharedHeaderFunctions
  import MaterialProviders.Client
  import opened EncryptedDataKeys
  import opened EncryptionContext
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  type V2HeaderBody = h: HeaderTypes.HeaderBody
  | h.V2HeaderBody?
  witness *

  function method WriteV2HeaderBody(
    body: V2HeaderBody
  )
    :(ret: seq<uint8>)
  {
    // Dafny has trouble
    // with associativity of concatenation
    // (knowing that (a + b) + c == a + (b + c) ).
    // So manually adding the () helps make it clear.
      WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V2)
    + (WriteESDKSuiteId(body.esdkSuiteId)
    + (WriteMessageId(body.messageId)
    + (WriteAADSection(body.encryptionContext)
    + (WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    + (WriteContentType(body.contentType)
    + (WriteUint32(body.frameLength)
    + (Write(body.suiteData))))))))
  }

  function method {:vcs_split_on_every_assert} ReadV2HeaderBody(
    buffer: ReadableBuffer,
    maxEdks: Option<int64>
  )
    :(res: ReadCorrect<V2HeaderBody>)
    ensures CorrectlyReadV2HeaderBody(buffer, res)
  {
    var version :- ReadMessageFormatVersion(buffer);
    :- Need(version.data.V2?, Error("Message version must be version 2."));

    var esdkSuiteId :- ReadESDKSuiteId(version.tail);
    var suiteId := GetAlgorithmSuiteId(esdkSuiteId.data);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    :- Need(suite.commitment.HKDF?, Error("Algorithm suite must support commitment."));

    var messageId :- ReadMessageIdV2(esdkSuiteId.tail);

    var encryptionContext :- EncryptionContext.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail, maxEdks);

    var contentType :- ReadContentType(encryptedDataKeys.tail);

    var frameLength :- ReadUInt32(contentType.tail);

    var suiteData :- Read(frameLength.tail, suite.commitment.outputKeyLength as nat);
    assert |suiteData.data| == suite.commitment.outputKeyLength as nat;

    var body:V2HeaderBody := HeaderTypes.V2HeaderBody(
      esdkSuiteId := esdkSuiteId.data,
      messageId := messageId.data,
      encryptionContext := encryptionContext.data,
      encryptedDataKeys := encryptedDataKeys.data,
      contentType := contentType.data,
      frameLength := frameLength.data,
      suiteData := suiteData.data
    );

    assert version.tail.start - buffer.start == 1;
    assert esdkSuiteId.tail.start - version.tail.start == 2;
    assert messageId.tail.start - esdkSuiteId.tail.start == 32;
    assert messageId.tail.start == buffer.start + headerBytesToAADStart;

    assert if IsExpandedAADSection(messageId.tail) then
      IsV2ExpandedAADSection(buffer)
    else
      !IsV2ExpandedAADSection(buffer);

    assert WriteMessageFormatVersion(version.data)
      + WriteESDKSuiteId(body.esdkSuiteId)
      + WriteMessageId(body.messageId)
      <= buffer.bytes[buffer.start..];

    assert if IsV2ExpandedAADSection(buffer) then
      WriteExpandedAADSection(body.encryptionContext) <= buffer.bytes[messageId.tail.start..]
    else
      WriteAADSection(body.encryptionContext) <= buffer.bytes[messageId.tail.start..];

    assert WriteEncryptedDataKeysSection(body.encryptedDataKeys)
      + WriteContentType(body.contentType)
      + WriteUint32(body.frameLength)
      + Write(body.suiteData)
      <= buffer.bytes[encryptionContext.tail.start..];

    assert if IsV2ExpandedAADSection(buffer) then
      WriteV2ExpandedAADSectionHeader(body) <= buffer.bytes[buffer.start..]
    else
      WriteV2HeaderBody(body) <= buffer.bytes[buffer.start..];

    Success(SuccessfulRead(body, suiteData.tail))
  }

  predicate CorrectlyReadV2HeaderBody(
    buffer: ReadableBuffer,
    res: ReadCorrect<V2HeaderBody>
  )
  {
    if IsV2ExpandedAADSection(buffer) then
      CorrectlyRead(buffer, res, WriteV2ExpandedAADSectionHeader)
    else
      CorrectlyRead(buffer, res, WriteV2HeaderBody)
  }

  // version + suiteId + messageId
  const headerBytesToAADStart := 1 + 2 + 32;
  predicate IsV2ExpandedAADSection(
    buffer: ReadableBuffer
  )
  {
    IsExpandedAADSection(MoveStart(buffer, headerBytesToAADStart))
  }

  // This is *not* a function method,
  // because it is *only* used for correctness.
  // This represents the sub-optimal encoding of AAD
  // where empty AAD is encoded with an extra 2 bytes.
  function WriteV2ExpandedAADSectionHeader(
    body: V2HeaderBody
  )
    :(ret: seq<uint8>)
  {
    // Dafny has trouble
    // with associativity of concatenation
    // (knowing that (a + b) + c == a + (b + c) ).
    // So manually adding the () helps make it clear.
      WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V2)
    + (WriteESDKSuiteId(body.esdkSuiteId)
    + (WriteMessageId(body.messageId)
    + (WriteExpandedAADSection(body.encryptionContext)
    + (WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    + (WriteContentType(body.contentType)
    + (WriteUint32(body.frameLength)
    + (Write(body.suiteData))))))))
  }
}
