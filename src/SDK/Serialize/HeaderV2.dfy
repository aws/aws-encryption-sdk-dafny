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

module HeaderV2 {
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

  type V2Header = h: Header.Header
  | h.body.HeaderBodyV2?
  witness *

  const VERSION_2: seq<uint8> := [0x01];

  function method WriteHeaderV2(
    header: V2Header
  ):
    (ret: seq<uint8>)
  {
    var canonicalEC := CanonicalEncryptionContext(header.body.encryptionContext);

    VERSION_2
    + UInt16ToSeq(header.body.esdkSuiteId)
    + header.body.messageId
    + WriteAADSection(canonicalEC)
    + WriteEncryptedDataKeys(header.body.encryptedDataKeys)
    + [header.body.contentType.Serialize()]
    + UInt32ToSeq(header.body.frameLength)
    + header.body.suiteData
  }


}