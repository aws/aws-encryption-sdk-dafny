include "../../src/SDK/Materials.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"

module {:extern "TestMaterials"} TestMaterials {
  import opened StandardLibrary
  import opened Materials
  import AlgorithmSuite

  method {:test} TestConcatDataKeyMaterialsHappy() returns (res: Result<()>)
  {
    var edk1 := EncryptedDataKey([], [1], [1]);
    var pdk := seq(32, i => 0);
    var krTrace1 := KeyringTraceEntry([1], [1], {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY});
    var datakeyMat1 := DataKeyMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, pdk, [edk1], [krTrace1]);

    var edk2 := EncryptedDataKey([], [2], [2]);
    var krTrace2 := KeyringTraceEntry([2], [2], {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT});
    var datakeyMat2 := DataKeyMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, pdk, [edk2], [krTrace2]);

    var concatenated := ConcatDataKeyMaterials(datakeyMat1, datakeyMat2);

    var _ :- Require(pdk == datakeyMat1.plaintextDataKey == datakeyMat2.plaintextDataKey == concatenated.plaintextDataKey);
    var _ :- Require(datakeyMat1.algorithmSuiteID == datakeyMat2.algorithmSuiteID == concatenated.algorithmSuiteID);
    var _ :- RequireEqual(datakeyMat1.encryptedDataKeys + datakeyMat2.encryptedDataKeys, concatenated.encryptedDataKeys);
    res :=  RequireEqual(datakeyMat1.keyringTrace + datakeyMat2.keyringTrace, concatenated.keyringTrace);
  }
}
