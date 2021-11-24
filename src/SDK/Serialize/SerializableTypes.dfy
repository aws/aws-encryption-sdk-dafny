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

  const VALID_IDS: set<uint16> := {0x0578, 0x0478, 0x0378, 0x0346, 0x0214, 0x0178, 0x0146, 0x0114, 0x0078, 0x0046, 0x0014};
  
  type ESDKAlgorithmSuiteId = id: uint16 | id in VALID_IDS witness *

  const SupportedAlgorithmSuites: map<Crypto.AlgorithmSuiteId, ESDKAlgorithmSuiteId> := map[
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF := 0x0014,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF := 0x0046,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF := 0x0078,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 := 0x0114,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 := 0x0146,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 := 0x0178,
    Crypto.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := 0x0214,
    Crypto.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := 0x0346,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := 0x0378,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY := 0x0478,
    Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384 := 0x0578
  ]

  function GetESDKAlgorithmSuiteId(
    suiteId: Crypto.AlgorithmSuiteId
  ):
    (res: ESDKAlgorithmSuiteId)
  {
    LemmaSupportedAlgorithmSuitesIsComplete(suiteId);
    SupportedAlgorithmSuites[suiteId]
  }

  function GetAlgorithmSuiteId(
    esdkId: ESDKAlgorithmSuiteId
  ):
    (res: Crypto.AlgorithmSuiteId)
  {
    var suiteId
    :|
      && suiteId in SupportedAlgorithmSuites
      && SupportedAlgorithmSuites[suiteId] == esdkId;
    suiteId
  }

  lemma LemmaSupportedAlgorithmSuitesIsComplete(id:Crypto.AlgorithmSuiteId)
    ensures id in SupportedAlgorithmSuites
  {}

}
