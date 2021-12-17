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
    && (h.headerAuth.AES_Mac?
    ==>
      && |h.headerAuth.headerIv| == h.suite.encrypt.ivLength as nat
      && |h.headerAuth.headerAuthTag| == h.suite.encrypt.tagLength as nat)
    && (h.suite.commitment.HKDF?
      ==>
        && h.body.HeaderBodyV2?
        && |h.body.suiteData| == h.suite.commitment.outputKeyLength as nat)
    && (!h.suite.commitment.HKDF?
      ==>
        && h.body.HeaderBodyV1?)
  witness *

  datatype MessageFormat = V1 | V2

  datatype HeaderBody = 
    | HeaderBodyV1(
      nameonly messageType: MessageType,
      nameonly esdkSuiteId: ESDKAlgorithmSuiteId,
      nameonly messageId: MessageID,
      nameonly encryptionContext: EncryptionContext2.ESDKCanonicalEncryptionContext,
      nameonly encryptedDataKeys: ESDKEncryptedDataKeys,
      nameonly contentType: ContentType,
      nameonly headerIvLength: nat,
      nameonly frameLength: uint32
    )
    | HeaderBodyV2(
      nameonly esdkSuiteId: ESDKAlgorithmSuiteId,
      nameonly messageId: MessageID,
      nameonly encryptionContext: EncryptionContext2.ESDKCanonicalEncryptionContext,
      nameonly encryptedDataKeys: ESDKEncryptedDataKeys,
      nameonly contentType: ContentType,
      nameonly frameLength: uint32,
      nameonly suiteData: seq<uint8>
    )

  datatype HeaderAuth =
  | AES_Mac(
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

}