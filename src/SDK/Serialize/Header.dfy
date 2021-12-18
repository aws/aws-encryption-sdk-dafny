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

module Header {
  import Aws.Crypto
  import Seq
  import MaterialProviders.Client
  import EncryptionContext2
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  datatype HeaderInfo = HeaderInfo(
    nameonly body: HeaderBody,
    nameonly rawHeader: seq<uint8>,
    nameonly suite: Client.AlgorithmSuites.AlgorithmSuite,
    nameonly headerAuth: HeaderAuth
  )

  type Header = h: HeaderInfo
  |
    && GetESDKAlgorithmSuiteId(h.suite.id) == h.body.esdkSuiteId
    && h.body.contentType.NonFramed? <==> 0 == h.body.frameLength
    && h.body.contentType.Framed? <==> 0 < h.body.frameLength
    && (h.headerAuth.AESMac?
    ==>
      && |h.headerAuth.headerIv| == h.suite.encrypt.ivLength as nat
      && |h.headerAuth.headerAuthTag| == h.suite.encrypt.tagLength as nat)
    && (h.suite.commitment.HKDF?
      ==>
        && h.body.V2HeaderBody?
        && |h.body.suiteData| == h.suite.commitment.outputKeyLength as nat)
    && (!h.suite.commitment.HKDF?
      ==>
        && h.body.V1HeaderBody?)
  witness *

  datatype MessageFormat = V1 | V2

  datatype HeaderBody = 
    | V1HeaderBody(
      nameonly messageType: MessageType,
      nameonly esdkSuiteId: ESDKAlgorithmSuiteId,
      nameonly messageId: MessageID,
      nameonly encryptionContext: EncryptionContext2.ESDKCanonicalEncryptionContext,
      nameonly encryptedDataKeys: ESDKEncryptedDataKeys,
      nameonly contentType: ContentType,
      nameonly headerIvLength: nat,
      nameonly frameLength: uint32
    )
    | V2HeaderBody(
      nameonly esdkSuiteId: ESDKAlgorithmSuiteId,
      nameonly messageId: MessageID,
      nameonly encryptionContext: EncryptionContext2.ESDKCanonicalEncryptionContext,
      nameonly encryptedDataKeys: ESDKEncryptedDataKeys,
      nameonly contentType: ContentType,
      nameonly frameLength: uint32,
      nameonly suiteData: seq<uint8>
    )

  datatype HeaderAuth =
  | AESMac(
    nameonly headerIv: seq<uint8>,
    nameonly headerAuthTag: seq<uint8>
  )

  datatype MessageType =
  | TYPE_CUSTOMER_AED
    {
    function method Serialize(): uint8 {
      match this
      case TYPE_CUSTOMER_AED => 0x80
    }
    static function method Get(x: uint8): Result<MessageType, string> {
      :- Need(x == 0x80 , "Unsupported ContentType value.");
      Success(
        match x
        case 0x80 => TYPE_CUSTOMER_AED
      )
    }
  }

  datatype ContentType =
  | NonFramed
  | Framed
  {
    function method Serialize(): uint8 {
      match this
      case NonFramed => 0x01
      case Framed => 0x02
    }
    static function method Get(x: uint8): Result<ContentType, string> {
      :- Need(x == 0x01 || x == 0x02, "Unsupported ContentType value.");
      Success(
        match x
        case 0x01 => NonFramed
        case 0x02 => Framed
      )
    }
  }

  const MESSAGE_ID_LEN := 16
  type MessageID = x: seq<uint8> 
  | |x| == MESSAGE_ID_LEN
  witness *

  const VERSION_1: seq<uint8> := [0x01];
  const VERSION_2: seq<uint8> := [0x02];
  type Version = s: seq<uint8>
  |
    || s == VERSION_1
    || s == VERSION_2
  witness VERSION_1

  function method WriteVersion(
    version: Version
  ):
    (ret: seq<uint8>)
  {
    version
  }

  function method ReadVersion(
    bytes: ReadableBytes
  )
    :(res: ReadCorrect<Version>)
    ensures CorrectlyRead(bytes, res, WriteVersion)
  {
    var Data(raw, tail) :- SerializeFunctions.Read(bytes, |VERSION_1|);
    :- Need(
        || raw == VERSION_1
        || raw == VERSION_2,
      Error("Unsupported message version."));
    var version: Version := raw;
    Success(Data(version, tail))
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
