include "../../../src/SDK/Keyring/MultiKeyring.dfy"
include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"

include "./TestKeyrings.dfy"

module TestMultiKeying {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import RawAESKeyringDef
  import EncryptionSuites
  import MultiKeyringDef
  import TestKeyrings
  import AlgorithmSuite
  import Materials
  import UTF8

  method {:test} TestOnEncryptOnDecryptWithGenerator() returns (r: Result<()>) {
    // TODO: mock children keyrings
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var child1Name :- UTF8.Encode("child1 Name");
    var child1Namespace :- UTF8.Encode("child1 Namespace");
    var child2Name :- UTF8.Encode("child2 Name");
    var child2namespace :- UTF8.Encode("child2 Namespace");
    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Name, child1Namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyringDef.RawAESKeyring(child2Name, child2namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyIDs := new [][child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, keyIDs);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    
    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey));
    var encryptionMaterialsOut :- multiKeyring.OnEncrypt(encryptionMaterialsIn);
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
    var decryptionMaterialsOut :- multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk1]);
    // Check plaintextDataKey is as expected
    expect decryptionMaterialsOut.plaintextDataKey == pdk;
    // Check keyringTrace is as expected
    expect |decryptionMaterialsOut.keyringTrace| == 1;
    expect decryptionMaterialsOut.keyringTrace[0] == child1Keyring.DecryptTraceEntry();

    // Second edk decryption
    decryptionMaterialsOut :- multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk2]);
    // Check plaintextDataKey is as expected
    expect decryptionMaterialsOut.plaintextDataKey == pdk;
    // Check keyringTrace is as expected
    expect |decryptionMaterialsOut.keyringTrace| == 1;
    expect decryptionMaterialsOut.keyringTrace[0] == child2Keyring.DecryptTraceEntry();
  }

  method {:test} TestOnEncryptOnDecryptWithoutGenerator() returns (r: Result<()>) {
    // TODO: mock children keyrings and move encrypt <-> decrypt test into new test
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var child1Name :- UTF8.Encode("child1 Name");
    var child1Namespace :- UTF8.Encode("child1 Namespace");
    var child2Name :- UTF8.Encode("child2 Name");
    var child2namespace :- UTF8.Encode("child2 Namespace");
    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Name, child1Namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new RawAESKeyringDef.RawAESKeyring(child2Name, child2namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
      
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);

    var keyIDs := new [][child1Keyring, child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, keyIDs);

    var pdk := seq(32, i => 0);
    var traceEntry := Materials.KeyringTraceEntry([], [], {Materials.GENERATED_DATA_KEY});
    
    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey))
                                                              .WithKeys(Some(pdk), [], [traceEntry]);
    var encryptionMaterialsOut :- multiKeyring.OnEncrypt(encryptionMaterialsIn);
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
    var materialsOut :- multiKeyring.OnDecrypt(materialsIn, [edk1]);
    // Check plaintextDataKey is as expected
    expect materialsOut.plaintextDataKey == Some(pdk);
    // Check keyringTrace is as expected
    expect |materialsOut.keyringTrace| == 1;
    expect && materialsOut.keyringTrace[0] == child1Keyring.DecryptTraceEntry();

    // Second EDK decryption
    materialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    materialsOut :- multiKeyring.OnDecrypt(materialsIn, [edk2]);
    // Check plaintextDataKey is as expected
    expect materialsOut.plaintextDataKey == Some(pdk);
    // Check keyringTrace is as expected
    expect |materialsOut.keyringTrace| == 1;
    expect materialsOut.keyringTrace[0] == child2Keyring.DecryptTraceEntry();
  }

  method {:test} TestOnEncryptChildKeyringFailure() returns (r: Result<()>) {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var child1Name :- UTF8.Encode("child1 Name");
    var child1Namespace :- UTF8.Encode("child1 Namespace");
    var child1Keyring := new RawAESKeyringDef.RawAESKeyring(child1Name, child1Namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var child2Keyring := new TestKeyrings.AlwaysFailingKeyring();
    var keyIDs := new [][child2Keyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(child1Keyring, keyIDs);
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    
    // Encryption
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, algorithmSuiteID, Some(signingKey));
    var encryptionMaterialsOut := multiKeyring.OnEncrypt(encryptionMaterialsIn);
    expect encryptionMaterialsOut.Failure?;
  }

  method {:test} TestOnDecryptNoChildDecryptsAndAtLeastOneFails() returns (r: Result<()>) {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var edk := Materials.EncryptedDataKey.ValidWitness();
    var verificationKey := seq(32, i => 0);

    var childKeyring1 := new TestKeyrings.AlwaysFailingKeyring();
    var childKeyring2 := new TestKeyrings.NoOpKeyring();
    var children := new [][childKeyring1, childKeyring2];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(childKeyring2, children);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var decryptionMaterialsOut := multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.Failure?;
  }

  method {:test} TestOnDecryptAllChildKeyringsDontDecrypt() returns (r: Result<()>) {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var edk := Materials.EncryptedDataKey.ValidWitness();
    var verificationKey := seq(32, i => 0);

    var childKeyring := new TestKeyrings.NoOpKeyring();
    var children := new [][childKeyring, childKeyring];
    var multiKeyring := new MultiKeyringDef.MultiKeyring(null, children);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, algorithmSuiteID, Some(verificationKey));
    var decryptionMaterialsOut :- multiKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.plaintextDataKey.None?;
  }
}
