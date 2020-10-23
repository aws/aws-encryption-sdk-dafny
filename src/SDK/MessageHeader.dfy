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
  import opened StandardLibrary
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
      && |auth.iv| == body.algorithmSuiteID.IVLength()
      && |auth.authenticationTag| == body.algorithmSuiteID.TagLength()
    }
  }

  /*
   * Header body type definition
   */

  const VERSION_1: uint8     := 0x01
  type Version               = x | x == VERSION_1 witness VERSION_1

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
    ensures var opt := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.get) == x
  {
  }

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Materials.EncryptedDataKey>)
  {
    predicate Valid() {
      && 0 < |entries| < UINT16_LIMIT
      && (forall i :: 0 <= i < |entries| ==> entries[i].Valid())
    }
  }

  datatype HeaderBody = HeaderBody(
                          version: Version,
                          typ: Type,
                          algorithmSuiteID: AlgorithmSuite.ID,
                          messageID: MessageID,
                          aad: EncryptionContext.Map,
                          encryptedDataKeys: EncryptedDataKeys,
                          contentType: ContentType,
                          ivLength: uint8,
                          frameLength: uint32)
  {
    predicate Valid() {
      && EncryptionContext.Serializable(aad)
      && encryptedDataKeys.Valid()
      && algorithmSuiteID.IVLength() == ivLength as nat
      && ValidFrameLength(frameLength, contentType)
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
    headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), _ => 0)        
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
    [hb.version as uint8] +
    [hb.typ as uint8] +
    UInt16ToSeq(hb.algorithmSuiteID as uint16) +
    hb.messageID +
    EncryptionContext.MapToLinear(hb.aad) +
    EDKsToSeq(hb.encryptedDataKeys) +
    [ContentTypeToUInt8(hb.contentType)] +
    Reserved +
    [hb.ivLength] +
    UInt32ToSeq(hb.frameLength)
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
    exists serializedAAD | EncryptionContext.LinearSeqToMap(serializedAAD, hb.aad) ::
      sequence == 
        [hb.version as uint8] +
        [hb.typ as uint8] +
        UInt16ToSeq(hb.algorithmSuiteID as uint16) +
        hb.messageID +
        serializedAAD + // This field can be encrypted in multiple ways and prevents us from reusing HeaderBodyToSeq
        EDKsToSeq(hb.encryptedDataKeys) +
        [ContentTypeToUInt8(hb.contentType)] +
        Reserved +
        [hb.ivLength] +
        UInt32ToSeq(hb.frameLength)
  }

  lemma IsSerializationOfHeaderBodyDuality(hb: HeaderBody)
    requires hb.Valid()
    ensures IsSerializationOfHeaderBody(HeaderBodyToSeq(hb), hb)
  {
    reveal HeaderBodyToSeq(), IsSerializationOfHeaderBody();
    EncryptionContext.MapToLinearIsDualLinearSeqToMap(hb.aad);
  }
}
