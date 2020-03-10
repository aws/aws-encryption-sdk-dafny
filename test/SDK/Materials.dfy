include "../../src/SDK/Materials.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"

module {:extern "TestMaterials"} TestMaterials {
  import opened StandardLibrary
  import opened Materials
  import AlgorithmSuite

  method {:test} TestWithKeysSettingPlaintextDataKey()
  {
    var encryptionContext := map[];
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterials1 := EncryptionMaterials(encryptionContext, algorithmSuiteID, None, [], [], Some(signingKey));

    var pdk := seq(32, i => 0);
    var edk := EncryptedDataKey([], [2], [2]);
    var krTrace := KeyringTraceEntry([2], [2], {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY});
    assert Materials.IsGenerateTraceEntry(krTrace);
    var encryptionMaterials2 := encryptionMaterials1.WithKeys(Some(pdk), [edk], [krTrace]);

    expect Some(pdk) == encryptionMaterials2.plaintextDataKey;
    expect encryptionMaterials1.algorithmSuiteID == encryptionMaterials2.algorithmSuiteID;
    expect [edk] == encryptionMaterials2.encryptedDataKeys;
    expect [krTrace] == encryptionMaterials2.keyringTrace;
  }

  method {:test} TestWithKeysKeepingPlaintextDataKey()
  {
    var encryptionContext := map[];
    var edk1 := EncryptedDataKey([], [1], [1]);
    var pdk := seq(32, i => 0);
    var krTrace1 := KeyringTraceEntry([1], [1], {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY});
    var algorithmSuiteID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterials1 := EncryptionMaterials(encryptionContext, algorithmSuiteID, Some(pdk), [edk1], [krTrace1], Some(signingKey));

    var edk2 := EncryptedDataKey([], [2], [2]);
    var krTrace2 := KeyringTraceEntry([2], [2], {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT});
    var encryptionMaterials2 := encryptionMaterials1.WithKeys(Some(pdk), [edk2], [krTrace2]);

    expect Some(pdk) == encryptionMaterials1.plaintextDataKey == encryptionMaterials2.plaintextDataKey;
    expect encryptionMaterials1.algorithmSuiteID == encryptionMaterials2.algorithmSuiteID;
    expect encryptionMaterials1.encryptedDataKeys + [edk2] == encryptionMaterials2.encryptedDataKeys;
    expect encryptionMaterials1.keyringTrace + [krTrace2] == encryptionMaterials2.keyringTrace;
  }
}
