// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsEncryptionSdkTypes.dfy"
include "SerializableTypes.dfy"
include "SerializeFunctions.dfy"
include "HeaderTypes.dfy"
include "SharedHeaderFunctions.dfy"
include "EncryptionContext.dfy"
include "EncryptedDataKeys.dfy"

module V1HeaderBody {
  import Types = AwsEncryptionSdkTypes
  import MaterialProviders
  import Seq
  import HeaderTypes
  import opened SharedHeaderFunctions
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

  //= compliance/data-format/message-header.txt#2.5.2.1
  //= type=implication
  //# A reserved sequence of 4 bytes that MUST have the value (hex) of "00
  //# 00 00 00".
  const RESERVED_BYTES: seq<uint8> := [0x00, 0x00, 0x00, 0x00];
  type ReservedBytes = s: seq<uint8>
  | s == RESERVED_BYTES
  witness RESERVED_BYTES

  function method WriteV1HeaderBody(
    body: V1HeaderBody
  )
    :(ret: seq<uint8>)
  {

    //= compliance/client-apis/encrypt.txt#2.6.2
    //# If the message format version associated with the algorithm suite
    //# (../framework/algorithm-suites.md#supported-algorithm-suites) is 1.0
    //# then the message header body (../data-format/message-
    //# header.md#header-body-version-1-0) MUST be serialized with the
    //# following specifics:

    // Dafny has trouble
    // with associativity of concatenation
    // (knowing that (a + b) + c == a + (b + c) ).
    // So manually adding the () helps make it clear.

    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Version (../data-format/message-header.md#version-1): MUST have a
    //# value corresponding to 1.0 (../data-format/message-
    //# header.md#supported-versions)
    WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V1)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Type (../data-format/message-header.md#type): MUST have a value
    //# corresponding to Customer Authenticated Encrypted Data (../data-
    //# format/message-header.md#supported-types)
    + (WriteV1MessageType(body.messageType)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Algorithm Suite ID (../data-format/message-header.md#algorithm-
    //# suite-id): MUST correspond to the algorithm suite (../framework/
    //# algorithm-suites.md) used in this behavior
    + (WriteESDKSuiteId(body.algorithmSuite)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Message ID (../data-format/message-header.md#message-id): The
    //# process used to generate this identifier MUST use a good source of
    //# randomness to make the chance of duplicate identifiers negligible.
    + (WriteMessageId(body.messageId)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  AAD (../data-format/message-header.md#aad): MUST be the
    //# serialization of the encryption context (../framework/
    //# structures.md#encryption-context) in the encryption materials
    //# (../framework/structures.md#encryption-materials)
    + (WriteAADSection(body.encryptionContext)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Encrypted Data Keys (../data-format/message-header.md#encrypted-
    //# data-key-entries): MUST be the serialization of the encrypted data
    //# keys (../framework/structures.md#encrypted-data-keys) in the
    //# encryption materials (../framework/structures.md#encryption-
    //# materials)
    + (WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Content Type (../data-format/message-header.md#content-type): MUST
    //# be 02 (../data-format/message-header.md#supported-content-types)
    + (WriteContentType(body.contentType)
    + (WriteV1ReservedBytes(RESERVED_BYTES)
    //= compliance/data-format/message-header.txt#2.5.2.2
    //# This value MUST be
    //# equal to the IV length (../framework/algorithm-suites.md#iv-length)
    //# value of the algorithm suite (../framework/algorithm-suites.md)
    //# specified by the Algorithm Suite ID (Section 2.5.1.5) field.
    //
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  IV Length (../data-format/message-header.md#iv-length): MUST match
    //# the IV length (../framework/algorithm-suites.md#iv-length)
    //# specified by the algorithm suite (../framework/algorithm-
    //# suites.md)
    + (WriteV1HeaderIvLength(GetIvLength(body.algorithmSuite))
    //= compliance/client-apis/encrypt.txt#2.6.2
    //# *  Frame Length (../data-format/message-header.md#frame-length): MUST
    //# be the value of the frame size determined above.
    + (WriteUint32(body.frameLength))))))))))
  }

  function method {:vcs_split_on_every_assert} ReadV1HeaderBody(
    buffer: ReadableBuffer,
    maxEdks: Option<Types.CountingNumbers>,
    mpl: MaterialProviders.MaterialProvidersClient
  )
    :(res: ReadCorrect<V1HeaderBody>)
    ensures CorrectlyReadV1HeaderBody(buffer, res)
  {
    var version :- ReadMessageFormatVersion(buffer);
    :- Need(version.data.V1?, Error("Message version must be version 1."));

    var messageType :- ReadV1MessageType(version.tail);

    var suite :- ReadESDKSuiteId(messageType.tail, mpl);
    :- Need(suite.data.commitment.None?, Error("Algorithm suite must not support commitment."));

    var messageId :- ReadMessageIdV1(suite.tail);

    var encryptionContext :- EncryptionContext.ReadAADSection(messageId.tail);

    var encryptedDataKeys :- EncryptedDataKeys.ReadEncryptedDataKeysSection(encryptionContext.tail, maxEdks);

    var contentType :- ReadContentType(encryptedDataKeys.tail);

    var reservedBytes :- ReadV1ReservedBytes(contentType.tail);

    var headerIvLength :- ReadV1HeaderIvLength(
      reservedBytes.tail,
      suite.data
    );

    var frameLength :- ReadUInt32(headerIvLength.tail);

    var body:V1HeaderBody := HeaderTypes.V1HeaderBody(
      messageType := messageType.data,
      algorithmSuite := suite.data,
      messageId := messageId.data,
      encryptionContext := encryptionContext.data,
      encryptedDataKeys := encryptedDataKeys.data,
      contentType := contentType.data,
      headerIvLength := headerIvLength.data as nat,
      frameLength := frameLength.data
    );

    assert CorrectlyReadV1HeaderBody(buffer, Success(SuccessfulRead(body, frameLength.tail))) by {
      assert WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V1) <= buffer.bytes[buffer.start..];
      if IsV1ExpandedAADSection(buffer) {
        assert 0 == |body.encryptionContext|;
        assert messageId.tail.start + 4 == encryptionContext.tail.start;
        assert WriteV1ExpandedAADSectionHeaderBody(body) <= buffer.bytes[buffer.start..];
      } else {
        if 0 < |body.encryptionContext| {
          HeadersAreTheSameWhenThereIsEncryptionContext(body);
          assert WriteV1ExpandedAADSectionHeaderBody(body) <= buffer.bytes[buffer.start..];
          assert WriteV1HeaderBody(body) <= buffer.bytes[buffer.start..];
        } else {
          assert messageId.tail.start + 2 == encryptionContext.tail.start;
          assert WriteV1HeaderBody(body) <= buffer.bytes[buffer.start..];
        }
      }
    }

    Success(SuccessfulRead(body, frameLength.tail))
  }

  predicate CorrectlyReadV1HeaderBody(
    buffer: ReadableBuffer,
    res: ReadCorrect<V1HeaderBody>
  )
  {
    if IsV1ExpandedAADSection(buffer) then
      CorrectlyRead(buffer, res, WriteV1ExpandedAADSectionHeaderBody)
    else
      CorrectlyRead(buffer, res, WriteV1HeaderBody)
  }

  predicate IsV1ExpandedAADSection(
    buffer: ReadableBuffer
  )
  {
    // version + messageType + suiteId + messageId
    var headerBytesToAADStart := 1 + 1 + 2 + 16;
    IsExpandedAADSection(MoveStart(buffer, headerBytesToAADStart))
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
    suite: MPL.AlgorithmSuiteInfo
  )
    :(res: ReadCorrect<uint8>)
    ensures CorrectlyRead(buffer, res, WriteV1HeaderIvLength)
  {
    var SuccessfulRead(raw, tail) :- SerializeFunctions.Read(buffer, 1);
    :- Need(raw[0] == GetIvLength(suite), Error("HeaderIv Length does not match Algorithm Suite."));
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

    // Dafny has trouble
    // with associativity of concatenation
    // (knowing that (a + b) + c == a + (b + c) ).
    // So manually adding the () helps make it clear.
      WriteMessageFormatVersion(HeaderTypes.MessageFormatVersion.V1)
    + (WriteV1MessageType(body.messageType)
    + (WriteESDKSuiteId(body.algorithmSuite)
    + (WriteMessageId(body.messageId)
    + (WriteExpandedAADSection(body.encryptionContext)
    + (WriteEncryptedDataKeysSection(body.encryptedDataKeys)
    + (WriteContentType(body.contentType)
    + (WriteV1ReservedBytes(RESERVED_BYTES)
    + (WriteV1HeaderIvLength(GetIvLength(body.algorithmSuite))
    + (WriteUint32(body.frameLength))))))))))
  }

  lemma HeadersAreTheSameWhenThereIsEncryptionContext(body: V1HeaderBody)
    requires 0 < |body.encryptionContext|
    ensures WriteV1ExpandedAADSectionHeaderBody(body) == WriteV1HeaderBody(body)
{}

}
