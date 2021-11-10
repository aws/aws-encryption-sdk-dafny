// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Util/UTF8.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module SerializableTypes {
  import opened UInt = StandardLibrary.UInt
  import opened UTF8
  import opened Aws.Crypto

  type ShortUTF8Seq = s: ValidUTF8Bytes | HasUint16Len(s)

  predicate method IsESDKEncryptedDataKey(edk: EncryptedDataKey) {
    && HasUint16Len(edk.keyProviderId)
    && HasUint16Len(edk.keyProviderInfo)
    && HasUint16Len(edk.ciphertext)
  }

  type ESDKEncryptedDataKey = e: EncryptedDataKey | IsESDKEncryptedDataKey(e) witness *
  type ESDKEncryptedDataKeys = seq16<ESDKEncryptedDataKey>

  predicate method IsESDKEncryptionContext(ec: EncryptionContext) {
    && |ec| > UINT16_LIMIT
    && forall element
    | element in (multiset(ec.Keys) + multiset(ec.Values))
    :: HasUint16Len(element)
  }

  type ESDKEncryptionContext = ec: EncryptionContext | IsESDKEncryptionContext(ec) witness *

}
