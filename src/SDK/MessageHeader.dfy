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
      && body.Valid()
      && |auth.iv| == body.AlgorithmSuite().IVLength()
      && |auth.authenticationTag| == body.AlgorithmSuite().TagLength()
    }
  }

  /*
   * Header body type definition
   */

  const VERSION_1: uint8     := 0x01
  const VERSION_2: uint8     := 0x02
  type Version               = x: uint8 | x == VERSION_1 || x == VERSION_2 witness VERSION_1

  const TYPE_CUSTOMER_AED: uint8 := 0x80
  type Type                  = x | x == TYPE_CUSTOMER_AED witness TYPE_CUSTOMER_AED

  const MESSAGE_ID_LEN       := 16
  type MessageID             = x: seq<uint8> | |x| == MESSAGE_ID_LEN witness [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

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
    predicate Valid() {
      && 0 < |entries| < UINT16_LIMIT
      && (forall i :: 0 <= i < |entries| ==> entries[i].Valid())
    }
  }

  datatype HeaderBodyCommon = HeaderBodyCommon(
    algorithmSuiteID: AlgorithmSuite.ID,
    messageID: MessageID,
    aad: EncryptionContext.Map,
    encryptedDataKeys: EncryptedDataKeys,
    contentType: ContentType,
    frameLength: uint32)
  {
    predicate Valid() {
      && EncryptionContext.Serializable(aad)
      && encryptedDataKeys.Valid()
      && ValidFrameLength(frameLength, contentType)
    }
  }
  datatype HeaderBody =
    | HeaderBodyV1(
        headerBodyCommon: HeaderBodyCommon,
        typ: Type,
        ivLength: uint8)
    | HeaderBodyV2(
        headerBodyCommon: HeaderBodyCommon,
        suiteData: seq<uint8>)
  {
    predicate Valid() {
      match this
      case HeaderBodyV1(headerBodyCommon, typ, ivLength) => (
        && headerBodyCommon.Valid()
        && AlgorithmSuite().IVLength() == ivLength as nat
      )
      case HeaderBodyV2(headerBodyCommon, suiteData) => (
        && headerBodyCommon.Valid()
        && AlgorithmSuite().SuiteDataLength() == Some(|suiteData|)
      )
    }

    function method AlgorithmSuite(): AlgorithmSuite.ID {
      this.headerBodyCommon.algorithmSuiteID
    }
  }

  /*
   * Header authentication type definition
   */
  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)

  predicate HeaderAuthenticationMatchesHeaderBody(headerAuthentication: HeaderAuthentication, headerBody: HeaderBody)
    requires headerBody.Valid()
  {
    var serializedHeaderBody := (reveal HeaderBodyToSeq(); HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.AlgorithmSuite().IVLength(), _ => 0)
    && exists encryptionOutput |
      AESEncryption.EncryptionOutputEncryptedWithAAD(encryptionOutput, serializedHeaderBody)
      && AESEncryption.CiphertextGeneratedWithPlaintext(encryptionOutput.cipherText, []) ::
        encryptionOutput.authTag == headerAuthentication.authenticationTag
  }

  predicate ValidFrameLength(frameLength: uint32, contentType: ContentType) {
    match contentType
    case NonFramed => frameLength == 0
    case Framed => frameLength != 0
  }

  /*
   * Specifications of serialized format
   */

  function {:opaque} HeaderBodyToSeq(hb: HeaderBody): seq<uint8>
    requires hb.Valid()
  {
    match hb
    case HeaderBodyV1(headerBodyCommon, typ, ivLength) => (
      [hb.AlgorithmSuite().MessageFormat() as uint8] +
      [hb.typ as uint8] +
      UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
      hb.headerBodyCommon.messageID +
      EncryptionContext.MapToLinear(hb.headerBodyCommon.aad) +
      EDKsToSeq(hb.headerBodyCommon.encryptedDataKeys) +
      [ContentTypeToUInt8(hb.headerBodyCommon.contentType)] +
      Reserved +
      [hb.ivLength] +
      UInt32ToSeq(hb.headerBodyCommon.frameLength)
    )
    case HeaderBodyV2(common, suiteData) => (
      [hb.AlgorithmSuite().MessageFormat() as uint8] +
      UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
      common.messageID +
      EncryptionContext.MapToLinear(common.aad) +
      EDKsToSeq(common.encryptedDataKeys) +
      [ContentTypeToUInt8(common.contentType)] +
      UInt32ToSeq(common.frameLength) +
      suiteData
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
    requires hb.Valid()
  {
    exists serializedAAD | EncryptionContext.LinearSeqToMap(serializedAAD, hb.headerBodyCommon.aad) ::
      IsSerializationOfHeaderBodyAux(sequence, hb, serializedAAD)
  }

  predicate IsSerializationOfHeaderBodyAux(sequence: seq<uint8>, hb: HeaderBody, serializedAAD: seq<uint8>)
    requires hb.Valid() && EncryptionContext.LinearSeqToMap(serializedAAD, hb.headerBodyCommon.aad)
  {
    sequence ==
      match hb
      case HeaderBodyV1(common, typ, ivLength) => (
        [hb.AlgorithmSuite().MessageFormat() as uint8] +
        [typ as uint8] +
        UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
        common.messageID +
        serializedAAD + // This field can be encrypted in multiple ways and prevents us from reusing HeaderBodyToSeq
        EDKsToSeq(common.encryptedDataKeys) +
        [ContentTypeToUInt8(common.contentType)] +
        Reserved +
        [ivLength] +
        UInt32ToSeq(common.frameLength)
      )
      case HeaderBodyV2(common, suiteData) => (
        [hb.AlgorithmSuite().MessageFormat() as uint8] +
        UInt16ToSeq(hb.AlgorithmSuite() as uint16) +
        common.messageID +
        serializedAAD +
        EDKsToSeq(common.encryptedDataKeys) +
        [ContentTypeToUInt8(common.contentType)] +
        UInt32ToSeq(common.frameLength) +
        suiteData
      )
  }

  lemma IsSerializationOfHeaderBodyDuality(hb: HeaderBody)
    requires hb.Valid()
    ensures IsSerializationOfHeaderBody(HeaderBodyToSeq(hb), hb)
  {
    reveal HeaderBodyToSeq(), IsSerializationOfHeaderBody();
    EncryptionContext.MapToLinearIsDualLinearSeqToMap(hb.headerBodyCommon.aad);
  }
}
