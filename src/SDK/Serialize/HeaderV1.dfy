// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
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
  import opened EncryptedDataKeys
  import opened EncryptionContext2
  import opened SerializableTypes
  import opened StandardLibrary.UInt
  import opened Wrappers
  import opened UTF8
  import opened SerializeFunctions

  type V1Header = h: Header.Header
  | h.body.HeaderBodyV1?
  witness *

  const VERSION_1: seq<uint8> := [0x01];

  function method WriteHeaderV1(
    header: V1Header
  ):
    (ret: seq<uint8>)
  {
    var connonicalEC := CanonicalEncryptionContext(header.body.encryptionContext);

    VERSION_1
    + header.body.messageType.Serialize()
    + UInt16ToSeq(header.body.esdkSuiteId)
    + header.body.messageId
    + WriteAADSection(connonicalEC)
    + WriteEncryptedDataKeys(header.body.encryptedDataKeys)
    + [header.body.contentType.Serialize()]
    + [0x00, 0x00, 0x00, 0x00]
    + UInt32ToSeq(header.body.frameLength)
    + header.body.suiteData
  }


}