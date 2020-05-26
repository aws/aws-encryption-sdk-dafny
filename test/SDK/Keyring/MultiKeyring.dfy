// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/SDK/Keyring/MultiKeyring.dfy"
include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/SDK/EncryptionContext.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../Util/TestUtils.dfy"

include "./TestKeyrings.dfy"

module TestMultiKeying {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyringDef
  import EncryptionContext
  import EncryptionSuites
  import MultiKeyringDef
  import TestKeyrings
  import AlgorithmSuite
  import Materials
  import TestUtils
  import UTF8

  method {:test} TestOnEncryptOnDecryptWithGenerator() {
    // TODO: mock children keyrings
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var child1Namespace, child1Name := TestUtils.NamespaceAndName(1);
    var child2namespace, child2Name := TestUtils.NamespaceAndName(2);

    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Namespace, child1Name, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyringDef.RawAESKeyring(child2namespace, child2Name, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, [child2Keyring]);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);

    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey));
    var encryptionMaterialsOut :- expect multiKeyring.OnEncrypt(encryptionMaterialsIn);
    // Check EDK list is as expected
    expect |encryptionMaterialsOut.encryptedDataKeys| == 2;
    // Check keyringTrace is as expected
    expect |encryptionMaterialsOut.keyringTrace| == 3;
    expect encryptionMaterialsOut.keyringTrace[0] == child1Keyring.GenerateTraceEntry();
    expect encryptionMaterialsOut.keyringTrace[1] == child1Keyring.EncryptTraceEntry();
    expect encryptionMaterialsOut.keyringTrace[2] == child2Keyring.EncryptTraceEntry();

    var pdk := encryptionMaterialsOut.plaintextDataKey;
    var edk1 := encryptionMaterialsOut.encryptedDataKeys[0];
    var edk2 := encryptionMaterialsOut.encryptedDataKeys[1];

    // First edk decryption
    var verificationKey := seq(32, i => 0);
    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var decryptionMaterialsOut :- expect multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk1]);
    // Check plaintextDataKey is as expected
    expect decryptionMaterialsOut.plaintextDataKey == pdk;
    // Check keyringTrace is as expected
    expect |decryptionMaterialsOut.keyringTrace| == 1;
    expect decryptionMaterialsOut.keyringTrace[0] == child1Keyring.DecryptTraceEntry();

    // Second edk decryption
    decryptionMaterialsOut :- expect multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk2]);
    // Check plaintextDataKey is as expected
    expect decryptionMaterialsOut.plaintextDataKey == pdk;
    // Check keyringTrace is as expected
    expect |decryptionMaterialsOut.keyringTrace| == 1;
    expect decryptionMaterialsOut.keyringTrace[0] == child2Keyring.DecryptTraceEntry();
  }

  method {:test} TestOnEncryptOnDecryptWithoutGenerator() {
    // TODO: mock children keyrings and move encrypt <-> decrypt test into new test
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var child1Namespace, child1Name := TestUtils.NamespaceAndName(1);
    var child2namespace, child2Name := TestUtils.NamespaceAndName(2);

    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Namespace, child1Name, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyringDef.RawAESKeyring(child2namespace, child2Name, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);

    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, [child1Keyring, child2Keyring]);

    var pdk := seq(32, i => 0);
    var traceEntry := Materials.KeyringTraceEntry([], [], {Materials.GENERATED_DATA_KEY});

    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey))
                                                              .WithKeys(Some(pdk), [], [traceEntry]);
    var encryptionMaterialsOut :- expect multiKeyring.OnEncrypt(encryptionMaterialsIn);
    // Check plaintextDataKey is as expected
    expect encryptionMaterialsOut.plaintextDataKey == Some(pdk);
    // Check keyringTrace is as expected
    expect |encryptionMaterialsOut.keyringTrace| == 3;
    expect encryptionMaterialsOut.keyringTrace[1] == child1Keyring.EncryptTraceEntry();
    expect encryptionMaterialsOut.keyringTrace[2] == child2Keyring.EncryptTraceEntry();

    var edk1 := encryptionMaterialsOut.encryptedDataKeys[0];
    var edk2 := encryptionMaterialsOut.encryptedDataKeys[1];
    var verificationKey := seq(32, i => 0);

    // First EDK decryption
    var materialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var materialsOut :- expect multiKeyring.OnDecrypt(materialsIn, [edk1]);
    // Check plaintextDataKey is as expected
    expect materialsOut.plaintextDataKey == Some(pdk);
    // Check keyringTrace is as expected
    expect |materialsOut.keyringTrace| == 1;
    expect && materialsOut.keyringTrace[0] == child1Keyring.DecryptTraceEntry();

    // Second EDK decryption
    materialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    materialsOut :- expect multiKeyring.OnDecrypt(materialsIn, [edk2]);
    // Check plaintextDataKey is as expected
    expect materialsOut.plaintextDataKey == Some(pdk);
    // Check keyringTrace is as expected
    expect |materialsOut.keyringTrace| == 1;
    expect materialsOut.keyringTrace[0] == child2Keyring.DecryptTraceEntry();
  }

  method {:test} TestOnEncryptChildKeyringFailure() {
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var child1Namespace, child1Name := TestUtils.NamespaceAndName(1);

    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Namespace, child1Name, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new TestKeyrings.AlwaysFailingKeyring();
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, [child2Keyring]);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);

    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey));
    var encryptionMaterialsOut := multiKeyring.OnEncrypt(encryptionMaterialsIn);
    expect encryptionMaterialsOut.Failure?;
  }

  method {:test} TestOnDecryptNoChildDecryptsAndAtLeastOneFails() {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var edk := Materials.EncryptedDataKey.ValidWitness();
    var verificationKey := seq(32, i => 0);

    var childKeyring1 := new TestKeyrings.AlwaysFailingKeyring();
    var childKeyring2 := new TestKeyrings.NoOpKeyring();
    var multiKeyring := new MultiKeyringDef.MultiKeyring(childKeyring2, [childKeyring1, childKeyring2]);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var decryptionMaterialsOut := multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.Failure?;
  }

  method {:test} TestOnDecryptAllChildKeyringsDontDecrypt() {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var edk := Materials.EncryptedDataKey.ValidWitness();
    var verificationKey := seq(32, i => 0);

    var childKeyring := new TestKeyrings.NoOpKeyring();
    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, [childKeyring, childKeyring]);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var decryptionMaterialsOut :- expect multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.plaintextDataKey.None?;
  }
}
