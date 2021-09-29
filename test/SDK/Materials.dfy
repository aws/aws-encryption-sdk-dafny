// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Materials.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"

module {:extern "TestMaterials"} TestMaterials {
  import opened Wrappers
  import opened Materials
  import AlgorithmSuite

  method {:test} TestWithKeysSettingPlaintextDataKey()
  {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterials1 := EncryptionMaterials(encryptionContext, algorithmSuiteID, None, [], Some(signingKey));

    var pdk := seq(32, i => 0);
    var edk := EncryptedDataKey([], [2], [2]);
    var encryptionMaterials2 := encryptionMaterials1.WithKeys(Some(pdk), [edk]);

    expect Some(pdk) == encryptionMaterials2.plaintextDataKey;
    expect encryptionMaterials1.algorithmSuiteID == encryptionMaterials2.algorithmSuiteID;
    expect [edk] == encryptionMaterials2.encryptedDataKeys;
  }

  method {:test} TestWithKeysKeepingPlaintextDataKey()
  {
    var encryptionContext := map[];
    var edk1 := EncryptedDataKey([], [1], [1]);
    var pdk := seq(32, i => 0);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterials1 := EncryptionMaterials(encryptionContext, algorithmSuiteID, Some(pdk), [edk1], Some(signingKey));

    var edk2 := EncryptedDataKey([], [2], [2]);
    var encryptionMaterials2 := encryptionMaterials1.WithKeys(Some(pdk), [edk2]);

    expect Some(pdk) == encryptionMaterials1.plaintextDataKey == encryptionMaterials2.plaintextDataKey;
    expect encryptionMaterials1.algorithmSuiteID == encryptionMaterials2.algorithmSuiteID;
    expect encryptionMaterials1.encryptedDataKeys + [edk2] == encryptionMaterials2.encryptedDataKeys;
  }
}
