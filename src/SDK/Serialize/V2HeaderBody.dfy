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

  function method ReadV2HeaderBody(
    buffer: ReadableBuffer,
    maxEdks: Option<int64>
  )
    :(res: ReadCorrect<V2HeaderBody>)
    ensures CorrectlyReadV2HeaderBody(buffer, res)
  {
    var version :- SharedHeaderFunctions.ReadMessageFormatVersion(buffer);
    :- Need(version.data.V2?, Error("Message version must be version 2."));

    var esdkSuiteId :- SharedHeaderFunctions.ReadESDKSuiteId(version.tail);
    var suiteId := GetAlgorithmSuiteId(esdkSuiteId.data);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    :- Need(suite.commitment.HKDF?, Error("Algorithm suite must support commitment."));

    var messageId :- SharedHeaderFunctions.ReadMessageIdV2(esdkSuiteId.tail);

    var encryptionContext :- EncryptionContext.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail, maxEdks);

    var contentType :- SharedHeaderFunctions.ReadContentType(encryptedDataKeys.tail);

    var frameLength :- ReadUInt32(contentType.tail);

    var suiteData :- Read(frameLength.tail, suite.commitment.outputKeyLength as nat);

    var body:V2HeaderBody := HeaderTypes.V2HeaderBody(
      esdkSuiteId := esdkSuiteId.data,
      messageId := messageId.data,
      encryptionContext := encryptionContext.data,
      encryptedDataKeys := encryptedDataKeys.data,
      contentType := contentType.data,
      frameLength := frameLength.data,
      suiteData := suiteData.data
    );

    Success(SuccessfulRead(body, suiteData.tail))
  }

  // TODO: This needs to be proven
  predicate CorrectlyReadV2HeaderBody(
    buffer: ReadableBuffer,
    res: ReadCorrect<V2HeaderBody>
  )
  {
    && res.Success? ==> CorrectlyReadRange(buffer, res.value.tail)
    && (
      || (
        !IsV2ExpandedAADSection(buffer)
        ==>
          && CorrectlyRead(buffer, res, WriteV2HeaderBody))
      // This is to handle the edge case in empty AAD see: `ReadAADSection`
      || (
          IsV2ExpandedAADSection(buffer)
        ==>
          && CorrectlyRead(buffer, res, WriteV2ExpandedAADSectionHeader)))
  }

  predicate IsV2ExpandedAADSection(
    buffer: ReadableBuffer
  )
  {
    var headerBytesToAADStart := 1+2+16;
    var aadStartPosition := buffer.start+headerBytesToAADStart;
    && aadStartPosition+4 < |buffer.bytes|
    && buffer.bytes[aadStartPosition..aadStartPosition+4] == [0,2,0,0]
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
    // Stacks at the end or the beginning seems to work,
    // but I found this to be slightly faster.
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
