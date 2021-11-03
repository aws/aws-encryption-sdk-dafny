// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "EncryptionContext.dfy"
include "Materials.dfy"
include "../Util/UTF8.dfy"
include "../Util/Sets.dfy"
include "../Crypto/AESEncryption.dfy"

module {:extern "MessageHeader"} MessageHeader {
  import AlgorithmSuite
  import Sets
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import EncryptionContext
  import Materials
  import UTF8
  import AESEncryption


  /*
   * Definition of the message header, i.e., the header body and the header authentication
   */

  datatype Header = Header(body: HeaderBody, auth: HeaderAuthentication)
  {
    predicate Valid() {
      && |auth.iv| == body.AlgorithmSuite().IVLength()
      && |auth.authenticationTag| == body.AlgorithmSuite().TagLength()
    }
  }

  /*
   * Header body type definition
   */

  const VERSION_1: uint8     := 0x01
  const VERSION_2: uint8     := 0x02
  //= compliance/data-format/message-header.txt#2.5.1.3
  //= type=implication
  //# The version (hex) of this field
  //# MUST be a value that exists in the following table:
  type Version               = x: uint8 | x == VERSION_1 || x == VERSION_2 witness *

  datatype VVersion = V1 | V2

  function method VersionToUInt8(version: VVersion): uint8 {
    match version
    case V1 => VERSION_1
    case V2 => VERSION_2
  }

  function method UInt8ToVersion(x: uint8): Result<VVersion, string> {
    if x == VERSION_1 then
      Success(VVersion.V1)
    else if x == VERSION_2 then
      Success(VVersion.V1)
    else
      Failure("unsupported version")
  }

  //= compliance/data-format/message-header.txt#2.5.1.4
  //= type=implication
  //# The type (hex) of this field MUST be
  //# a value that exists in the following table:
  const TYPE_CUSTOMER_AED: uint8 := 0x80
  type Type                  = x | x == TYPE_CUSTOMER_AED witness TYPE_CUSTOMER_AED

  const MESSAGE_ID_LEN       := 16
  type MessageID             = x: seq<uint8> | |x| == MESSAGE_ID_LEN witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

  //= compliance/data-format/message-header.txt#2.5.2.1
  //= type=implication
  //# A reserved sequence of 4 bytes that MUST have the value (hex) of "00
  //# 00 00 00".
  const Reserved: seq<uint8> := [0,0,0,0]

  datatype ContentType       = NonFramed | Framed

  function method ContentTypeToUInt8(contentType: ContentType): uint8 {
    match contentType
    case NonFramed => 0x01
    case Framed => 0x02
  }

  function method UInt8ToContentType(x: uint8): Option<ContentType> {
    if x == 0x01 then
      Some(NonFramed)
    else if x == 0x02 then
      Some(Framed)
    else
      None
  }

  lemma ContentTypeConversionsCorrect(contentType: ContentType, x: uint8)
    ensures UInt8ToContentType(ContentTypeToUInt8(contentType)) == Some(contentType)
    ensures var opt := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.value) == x
  {
  }

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Materials.EncryptedDataKey>)
  {
    predicate method Valid() {
      //= compliance/data-format/message-header.txt#2.5.1.9
      //# This value MUST be greater than
      //# 0.
      && 0 < |entries| < UINT16_LIMIT
      && (forall i :: 0 <= i < |entries| ==> entries[i].Valid())
    }
  }

  datatype HeaderBodyV1' = HeaderBodyV1'(
    version: VVersion,
    typ: Type,
    algorithmSuiteID: AlgorithmSuite.ID,
    //= compliance/data-format/message-header.txt#2.5.1.6
    //# A Message ID MUST uniquely identify the message (message.md).
    messageID: MessageID,
    aad: EncryptionContext.Map,
    encryptedDataKeys: EncryptedDataKeys,
    contentType: ContentType,
    ivLength: uint8,
    frameLength: uint32
  )
  {
    predicate method Valid() {
      && EncryptionContext.Serializable(aad)
      && (
          //= compliance/data-format/message-header.txt#2.5.1.7.1
          //# When the encryption context (../framework/structures.md#encryption-
          //# context) is empty, the value of this field MUST be 0.
          || (|aad| == 0 && EncryptionContext.Length(aad) == 0)
          //= compliance/data-format/message-header.txt#2.5.1.7.2.1
          //# The value of this field MUST be greater
          //# than 0.
          || (|aad|  > 0 && EncryptionContext.Length(aad) > 0)
         )
      && encryptedDataKeys.Valid()
      && ValidFrameLength(frameLength, contentType)
      //= compliance/data-format/message-header.txt#2.5.2.2
      //# This value MUST be
      //# equal to the IV length (../framework/algorithm-suites.md#iv-length)
      //# value of the algorithm suite (../framework/algorithm-suites.md)
      //# specified by the Algorithm Suite ID (Section 2.5.1.5) field.
      && algorithmSuiteID.IVLength() == ivLength as nat
    }
  }

  type HeaderBodyV1 = h: HeaderBodyV1' | h.Valid() witness *

  datatype HeaderBodyV2' = HeaderBodyV2'(
    version: VVersion,
    algorithmSuiteID: AlgorithmSuite.ID,
    //= compliance/data-format/message-header.txt#2.5.1.6
    //# A Message ID MUST uniquely identify the message (message.md).
    messageID: MessageID,
    aad: EncryptionContext.Map,
    encryptedDataKeys: EncryptedDataKeys,
    contentType: ContentType,
    frameLength: uint32,
    suiteData: seq<uint8>
  )
  {
    predicate method Valid() {
      && EncryptionContext.Serializable(aad)
      //= compliance/data-format/message-header.txt#2.5.1.7.2.1
      //# The value of this field MUST be greater
      //# than 0.
      && EncryptionContext.Length(aad) > 0
      && encryptedDataKeys.Valid()
      && ValidFrameLength(frameLength, contentType)
      && algorithmSuiteID.SuiteDataLength() == Some(|suiteData|)
    }
  }

  type HeaderBodyV2 = h: HeaderBodyV2' | h.Valid() witness *

  datatype HeaderBody =
    | V1(hb1: HeaderBodyV1)
    | V2(hb2: HeaderBodyV2)
  {
    function method Version(): VVersion {
      match this
      case V1(h) => h.version
      case V2(h) => h.version
    }

    function method AlgorithmSuite(): AlgorithmSuite.ID {
      match this
      case V1(h) => h.algorithmSuiteID
      case V2(h) => h.algorithmSuiteID
    }

    function method AAD(): EncryptionContext.Map {
      match this
      case V1(h) => h.aad
      case V2(h) => h.aad
    }
  }

  /*
   * Header authentication type definition
   */
  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)

  predicate HeaderAuthenticationMatchesHeaderBody(headerAuthentication: HeaderAuthentication, headerBody: HeaderBody)
  {
    var serializedHeaderBody := (reveal HeaderBodyToSeq(); HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.AlgorithmSuite().IVLength(), _ => 0)
    && exists encryptionOutput |
      AESEncryption.EncryptionOutputEncryptedWithAAD(encryptionOutput, serializedHeaderBody)
      && AESEncryption.CiphertextGeneratedWithPlaintext(encryptionOutput.cipherText, []) ::
        encryptionOutput.authTag == headerAuthentication.authenticationTag
  }


  predicate method ValidFrameLength(frameLength: uint32, contentType: ContentType) {
    //= compliance/data-format/message-header.txt#2.5.2.3
    //# When the content type (Section 2.5.1.11) is non-
    //# framed, the value of this field MUST be 0.
    match contentType
    case NonFramed => frameLength == 0
    case Framed => frameLength != 0
  }

  /*
   * Specifications of serialized format
   */

  function {:opaque} HeaderBodyToSeq(hb: HeaderBody): seq<uint8>
  {
    match hb
    //= compliance/data-format/message-header.txt#2.5.1.1
    //# +===========+=====================+================================+
    //# | Field     | Length (bytes)      | Interpreted as                 |
    //# +===========+=====================+================================+
    //# | Section   | 1                   | See Supported Versions         |
    //# | 2.1       |                     | (Section 2.5.1.3.1) (MUST be   |
    //# |           |                     | "01" in version 1.0 Headers)   |
    //# +-----------+---------------------+--------------------------------+
    //# | Section   | 1                   | See Supported Types            |
    //# | 2.5.1.4   |                     | (Section 2.5.1.4.1)            |
    //# +-----------+---------------------+--------------------------------+
    //# | Algorithm | 2                   | See Supported Algorithm Suites |
    //# | Suite ID  |                     | (../framework/algorithm-       |
    //# | (Section  |                     | suites.md#supported-algorithm- |
    //# | 2.5.1.5)  |                     | suites)                        |
    //# +-----------+---------------------+--------------------------------+
    //# | Message   | 16                  | Bytes                          |
    //# | ID        |                     |                                |
    //# | (Section  |                     |                                |
    //# | 2.5.1.6)  |                     |                                |
    //# +-----------+---------------------+--------------------------------+
    //# | Section   | Variable.
    case V1(h) => (
      [h.algorithmSuiteID.MessageFormat() as uint8] +
      [h.typ as uint8] +
      //= compliance/data-format/message-header.txt#2.5.1.5
      //# The value (hex) of this field MUST be a value that exists
      //# in the Supported Algorithm Suites (../framework/algorithm-
      //# suites.md#supported-algorithm-suites) table.
      UInt16ToSeq(h.algorithmSuiteID as uint16) +
      h.messageID +
      EncryptionContext.MapToLinear(h.aad) +
      EDKsToSeq(h.encryptedDataKeys) +
      [ContentTypeToUInt8(h.contentType)] +
      Reserved +
      [h.ivLength] +
      UInt32ToSeq(h.frameLength)
    )

    //= compliance/data-format/message-header.txt#2.5.1.2
    //# +===========+=====================+================================+
    //# | Field     | Length (bytes)      | Interpreted as                 |
    //# +===========+=====================+================================+
    //# | Section   | 1                   | See Supported Versions         |
    //# | 2.1       |                     | (Section 2.5.1.3.1) (MUST be   |
    //# |           |                     | "02" in version 2.0 Headers)   |
    //# +-----------+---------------------+--------------------------------+
    //# | Algorithm | 2                   | See Supported Algorithm Suites |
    //# | Suite ID  |                     | (../framework/algorithm-       |
    //# | (Section  |                     | suites.md#supported-algorithm- |
    //# | 2.5.1.5)  |                     | suites)                        |
    //# +-----------+---------------------+--------------------------------+
    //# | Message   | 16                  | Bytes                          |
    //# | ID        |                     |                                |
    //# | (Section  |                     |                                |
    //# | 2.5.1.6)  |                     |                                |
    //# +-----------+---------------------+--------------------------------+
    //# | Section   | Variable.
    case V2(h) => (
      [h.algorithmSuiteID.MessageFormat() as uint8] +
      //= compliance/data-format/message-header.txt#2.5.1.5
      //# The value (hex) of this field MUST be a value that exists
      //# in the Supported Algorithm Suites (../framework/algorithm-
      //# suites.md#supported-algorithm-suites) table.
      UInt16ToSeq(h.algorithmSuiteID as uint16) +
      h.messageID +
      EncryptionContext.MapToLinear(h.aad) +
      EDKsToSeq(h.encryptedDataKeys) +
      [ContentTypeToUInt8(h.contentType)] +
      UInt32ToSeq(h.frameLength) +
      h.suiteData
    )
  }

  function EDKsToSeq(encryptedDataKeys: EncryptedDataKeys): seq<uint8>
    requires encryptedDataKeys.Valid()
  {
    var n := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) +
    EDKEntriesToSeq(encryptedDataKeys.entries, 0, n)
  }

  function EDKEntriesToSeq(entries: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
  {
    if lo == hi then [] else EDKEntriesToSeq(entries, lo, hi - 1) + EDKEntryToSeq(entries[hi - 1])
  }

  lemma EDKEntriesToSeqInductiveStep(entriesHead: seq<Materials.EncryptedDataKey>, entriesTail: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat)
    requires var entries := entriesHead + entriesTail;
      forall i :: 0 <= i < |entries| ==> (entries)[i].Valid()
    requires lo <= hi <= |entriesHead|
    ensures forall i :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid()
    ensures var entries := entriesHead + entriesTail;
      EDKEntriesToSeq(entriesHead + entriesTail, lo, hi) == EDKEntriesToSeq(entriesHead, lo, hi)
  {
    assert forall i :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid() by {
      if !(forall i :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid()) {
        var entry :| entry in entriesHead && !entry.Valid();
        assert entry in (entriesHead + entriesTail);
        assert false;
      }
    }
  }

  function method EDKEntryToSeq(edk: Materials.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
  {
    UInt16ToSeq(|edk.providerID| as uint16)   + edk.providerID +
    UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo +
    UInt16ToSeq(|edk.ciphertext| as uint16)   + edk.ciphertext
  }

  predicate {:opaque} IsSerializationOfHeaderBody(sequence: seq<uint8>, hb: HeaderBody)
  {
    exists serializedAAD | EncryptionContext.LinearSeqToMap(serializedAAD, hb.AAD()) ::
      IsSerializationOfHeaderBodyAux(sequence, hb, serializedAAD)
  }

  predicate IsSerializationOfHeaderBodyAux(sequence: seq<uint8>, hb: HeaderBody, serializedAAD: seq<uint8>)
    requires EncryptionContext.LinearSeqToMap(serializedAAD, hb.AAD())
  {
    sequence ==
      match hb
      case V1(h) => (
        [h.algorithmSuiteID.MessageFormat() as uint8] +
        [h.typ as uint8] +
        UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
        h.messageID +
        serializedAAD + // This field can be encrypted in multiple ways and prevents us from reusing HeaderBodyToSeq
        EDKsToSeq(h.encryptedDataKeys) +
        [ContentTypeToUInt8(h.contentType)] +
        Reserved +
        [h.ivLength] +
        UInt32ToSeq(h.frameLength)
      )
      case V2(h) => (
        [hb.AlgorithmSuite().MessageFormat() as uint8] +
        UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
        h.messageID +
        serializedAAD +
        EDKsToSeq(h.encryptedDataKeys) +
        [ContentTypeToUInt8(h.contentType)] +
        UInt32ToSeq(h.frameLength) +
        h.suiteData
      )
  }

  lemma IsSerializationOfHeaderBodyDuality(hb: HeaderBody)
    ensures IsSerializationOfHeaderBody(HeaderBodyToSeq(hb), hb)
  {
    reveal HeaderBodyToSeq(), IsSerializationOfHeaderBody();
    EncryptionContext.MapToLinearIsDualLinearSeqToMap(hb.AAD());
  }
}
