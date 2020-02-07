include "../../src/SDK/Materials.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"

module {:extern "TestMaterials"} TestMaterials {
  import opened StandardLibrary
  import opened Materials
  import AlgorithmSuite

  method {:test} TestEncryptionContextGetHappy() returns (res: Result<()>)
  {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");

    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");
    var encCtx := [(keyA, valA), (keyB, valB)];

    var val :- EncryptionContextGet(encCtx, keyA);
    var _ :- RequireEqual(val, valA);

    val :- EncryptionContextGet(encCtx, keyB);
    res := RequireEqual(val, valB);
  }

  method {:test} TestEncryptionContextGetSad() returns (res: Result<()>)
  {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");

    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");

    var badKey :- UTF8.Encode("Not a key");
    var encCtx := [(keyA, valA), (keyB, valB)];

    var methodCall := EncryptionContextGet(encCtx, badKey);
    res := RequireFailure(methodCall);
  }

  method {:test} TestEncryptionContextGetLarge() returns (res: Result<()>)
  {
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");

    var keyB :- UTF8.Encode("keyB");
    var valB :- UTF8.Encode("valB");
    // (2^16 - 1) / (minimum kvPair size) => (2^16 - 1) / 6 => 10922 is the max
    // number of pairs you can stuff into a valid AAD
    // We leave space for just one at the end.
    var encCtx := seq(10921, _ => (keyA, valA)) + [(keyB, valB)];

    var val :- EncryptionContextGet(encCtx, keyB);
    res := RequireEqual(valB, val);
  }

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
