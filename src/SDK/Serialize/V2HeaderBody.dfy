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

module V2HeaderBody {
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

  type V2HeaderBody = h: Header.HeaderBody
  | h.V1HeaderBody?
  witness *

  function method WriteV2HeaderBody(
    body: V2HeaderBody
  )
    :(ret: seq<uint8>)
  {

    Header.WriteVersion(Header.VERSION_2)
    + Header.WriteESDKSuiteId(body.esdkSuiteId)
    + Header.WriteMessageId(body.messageId)
    + WriteAADSection(body.encryptionContext)
    + WriteEncryptedDataKeys(body.encryptedDataKeys)
    + Header.WriteContentType(body.contentType)
    + UInt32ToSeq(body.frameLength)
    + Write(body.suiteData)
  }

  function method ReadV2HeaderBody(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<V2HeaderBody>)
    ensures
      || CorrectlyRead(bytes, res, WriteV2HeaderBody)
      // This is to handle the edge case in empty AAD see: `ReadAADSection`
      || (
        var headerBytesToAADStart := 1+2+16;
        var aadStartPosition := bytes.start+headerBytesToAADStart;
        && res.Success?
        && aadStartPosition+4 < |bytes.data|
        && bytes.data[aadStartPosition..aadStartPosition+4] == [0,2,0,0]
        ==>
          && CorrectlyRead(bytes, res, WriteV2ExpandedAADSectionHeader))

  {
    var version :- Header.ReadVersion(bytes);
    :- Need(version.thing == Header.VERSION_2, Error("Message version must be version 1."));

    var esdkSuiteId :- Header.ReadESDKSuiteId(version.tail);
    var suiteId := GetAlgorithmSuiteId(esdkSuiteId.thing);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    :- Need(suite.commitment.HKDF?, Error("Algorithm suite must support commitment."));

    var messageId :- Header.ReadMessageId(esdkSuiteId.tail);

    var encryptionContext :- EncryptionContext2.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail);

    var contentType :- Header.ReadContentType(encryptedDataKeys.tail);

    var frameLength :- ReadUInt32(contentType.tail);

    var suiteData :- Read(frameLength.tail, suite.commitment.outputKeyLength as nat);

    var body:V2HeaderBody := Header.V2HeaderBody(
      esdkSuiteId := esdkSuiteId.thing,
      messageId := messageId.thing,
      encryptionContext := encryptionContext.thing,
      encryptedDataKeys := encryptedDataKeys.thing,
      contentType := contentType.thing,
      frameLength := frameLength.thing,
      suiteData := suiteData.thing
    );

    Success(Data(body, frameLength.tail))
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

    Header.WriteVersion(Header.VERSION_2)
    + Header.WriteESDKSuiteId(body.esdkSuiteId)
    + Header.WriteMessageId(body.messageId)
    + WriteExpandedAADSection(body.encryptionContext)
    + WriteEncryptedDataKeys(body.encryptedDataKeys)
    + Header.WriteContentType(body.contentType)
    + UInt32ToSeq(body.frameLength)
    + Write(body.suiteData)
  }
}
