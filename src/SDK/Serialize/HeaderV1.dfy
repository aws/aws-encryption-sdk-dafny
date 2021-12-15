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
  const RESERVED_BYTES: seq<uint8> := [0x00, 0x00, 0x00, 0x00];

  function method WriteHeaderBodyV1(
    body: V1HeaderBody
  ):
    (ret: seq<uint8>)
  {
    var connonicalEC := CanonicalEncryptionContext(body.encryptionContext);
    var suiteId := GetAlgorithmSuiteId(body.esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);

    VERSION_1
    + [body.messageType.Serialize()]
    + UInt16ToSeq(body.esdkSuiteId)
    + body.messageId
    + WriteAADSection(connonicalEC)
    + WriteEncryptedDataKeys(body.encryptedDataKeys)
    + [body.contentType.Serialize()]
    + RESERVED_BYTES
    + [suite.encrypt.ivLength]
    + UInt32ToSeq(body.frameLength)
  }

  function method ReadHeaderBodyV1(
    s: seq<uint8>,
    pos: nat
  ):
    (res: ReadCorrect<V1HeaderBody>)
    ensures CorrectlyRead(s, pos, res, WriteHeaderBodyV1)
  {
    var (version, messageTypeStart) :- SerializeFunctions.Read(s, pos, 1);

    :- Need(version == VERSION_1, Error("Incorrect message version."));
    var (messageTypeByte, suiteStart) :- Read(s, messageTypeStart, 1);
    var messageType :- Header.MessageType.Get(messageTypeByte[0]).MapFailure(e => Error(e));
    var (esdkSuiteId, messageIdStart) :- ReadUInt16(s, suiteStart);
    :- Need(esdkSuiteId in VALID_IDS, Error("Algorithm suite not supported."));
    var suiteId := GetAlgorithmSuiteId(esdkSuiteId);
    var suite := Client.SpecificationClient().GetSuite(suiteId);
    var (messageId, ecStart) :- Read(s, messageIdStart, Header.MESSAGE_ID_LEN);
    var (canonicalEncryptionContext, edkStart) :- EncryptionContext2.ReadAADSection(s, ecStart);
    var encryptionContext: ESDKEncryptionContext := EncryptionContext2.EncryptionContext(canonicalEncryptionContext);
    var (encryptedDataKeys, contentTypeStart) :- EncryptedDataKeys.ReadEncryptedDataKeysSection(s, edkStart);
    var (contentTypeByte, reservedStart) :- Read(s, contentTypeStart, 1);
    var contentType :- Header.ContentType.Get(contentTypeByte[0]).MapFailure(e => Error(e));
    var (reservedBytes, headerIvLengthStart) :- Read(s, reservedStart, 4);
    :- Need(RESERVED_BYTES == reservedBytes, Error("Invalid Reserved Bytes"));
    var (headerIvLengthByte, frameLengthStart) :- Read(s, headerIvLengthStart, 1);
    var headerIvLength := headerIvLengthByte[0];
    :- Need(headerIvLength == suite.encrypt.ivLength, Error("Invalid IVLength."));
    var (frameLength, end) :- ReadUInt32(s, frameLengthStart);

    var body:V1HeaderBody := Header.HeaderBodyV1(
      messageType := messageType,
      esdkSuiteId := esdkSuiteId,
      messageId := messageId,
      encryptionContext := encryptionContext,
      encryptedDataKeys := encryptedDataKeys,
      contentType := contentType,
      headerIvLength := headerIvLength as nat,
      frameLength := frameLength
    );

    Success((body, end))
  }

}