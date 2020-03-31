include "../../src/SDK/Materials.dfy"
include "../../src/SDK/AlgorithmSuite.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../Util/TestUtils.dfy"

module {:extern "DefaultCMMTests"} DefaultCMMTests {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import DefaultCMMDef
  import Materials
  import EncryptionContext
  import UTF8
  import TestUtils

  method {:test} TestDefaultCMMNoAlg() returns (res: Result<()>) {
    var keyring :- TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    var encCtx: EncryptionContext.Map := map[];
    var getEncMatOutput :- cmm.GetEncryptionMaterials(Materials.EncryptionMaterialsRequest(encCtx, None, None));

    expect getEncMatOutput.algorithmSuiteID == 0x0378, "GetEncryptionMaterials returned unexpected algorithm id";
    expect |getEncMatOutput.encryptedDataKeys| > 0, "GetEncryptionMaterials didn't return any EDKs";
    expect getEncMatOutput.algorithmSuiteID.SignatureType().Some?, "GetEncryptionMaterials didn't return a signature algorithm";
    expect getEncMatOutput.signingKey.Some?, "GetEncryptionMaterials didn't return a signing key";

    var decMatRequest := Materials.DecryptionMaterialsRequest(getEncMatOutput.algorithmSuiteID, getEncMatOutput.encryptedDataKeys, getEncMatOutput.encryptionContext);
    var decMatOutput :- cmm.DecryptMaterials(decMatRequest);

    expect decMatOutput.plaintextDataKey.Some?, "DecryptMaterials did not return a plaintext datakey";
    expect decMatOutput.algorithmSuiteID.ValidPlaintextDataKey(decMatOutput.plaintextDataKey.get), "DecryptMaterials returned invalid plaintext datakey";
    expect decMatOutput.verificationKey.Some?, "DecryptMaterials did not return a verification key";

    return Success(());
  }

  method {:test} TestDefaultCMMWithAlg() returns (res: Result<()>) {
    var keyring :- TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    var encCtx: EncryptionContext.Map := map[];
    var getEncMatOutput :- cmm.GetEncryptionMaterials(Materials.EncryptionMaterialsRequest(encCtx, Some(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384), None));

    expect getEncMatOutput.algorithmSuiteID == AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
        "GetEncryptionMaterials returned the incorrect algorithm id";
    expect |getEncMatOutput.encryptedDataKeys| > 0, "GetEncryptionMaterials didn't return any EDKs";
    expect getEncMatOutput.algorithmSuiteID.SignatureType().Some?, "GetEncryptionMaterials didn't return a signature algorithm";
    expect getEncMatOutput.signingKey.Some?, "GetEncryptionMaterials didn't return a signing key";

    var decMatRequest := Materials.DecryptionMaterialsRequest(getEncMatOutput.algorithmSuiteID, getEncMatOutput.encryptedDataKeys, getEncMatOutput.encryptionContext);
    var decMatOutput :- cmm.DecryptMaterials(decMatRequest);

    expect decMatOutput.plaintextDataKey.Some?, "DecryptMaterials did not return a plaintext datakey";
    expect decMatOutput.algorithmSuiteID.ValidPlaintextDataKey(decMatOutput.plaintextDataKey.get), "DecryptMaterials returned invalid plaintext datakey";
    expect decMatOutput.verificationKey.Some?, "DecryptMaterials did not return a verification key";

    return Success(());
  }

  method {:test} TestDefaultCMMWithAlgNoSig() returns (res: Result<()>) {
    var keyring :- TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var encCtx: EncryptionContext.Map := map[];
    var getEncMatOutput :- cmm.GetEncryptionMaterials(Materials.EncryptionMaterialsRequest(encCtx, Some(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG), None));

    expect getEncMatOutput.algorithmSuiteID == AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG,
        "GetEncryptionMaterials returned the incorrect algorithm id";
    expect |getEncMatOutput.encryptedDataKeys| > 0, "GetEncryptionMaterials didn't return any EDKs";
    expect getEncMatOutput.algorithmSuiteID.SignatureType().None?, "GetEncryptionMaterials returned a signature algorithm when it shouldn't have";
    expect getEncMatOutput.signingKey.None?, "GetEncryptionMaterials returned a signing key when it shouldn't have";

    var decMatRequest := Materials.DecryptionMaterialsRequest(getEncMatOutput.algorithmSuiteID, getEncMatOutput.encryptedDataKeys, getEncMatOutput.encryptionContext);
    var decMatOutput :- cmm.DecryptMaterials(decMatRequest);

    expect decMatOutput.plaintextDataKey.Some?, "DecryptMaterials did not return a plaintext datakey";
    expect decMatOutput.algorithmSuiteID.ValidPlaintextDataKey(decMatOutput.plaintextDataKey.get), "DecryptMaterials returned invalid plaintext datakey";
    expect decMatOutput.verificationKey.None?, "DecryptMaterials erroneously returned a verification key";

    return Success(());
  }

  method {:test} TestDefaultCMMRejectsBadEncCtx() returns (res: Result<()>) {
    var keyring :- TestUtils.MakeRSAKeyring();
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
    var encCtx: EncryptionContext.Map := map[];
    encCtx := encCtx[Materials.EC_PUBLIC_KEY_FIELD := [0x00]];
    var shouldBeFail := cmm.GetEncryptionMaterials(Materials.EncryptionMaterialsRequest(encCtx, None, None));

    expect shouldBeFail.Failure?, "GetEncryptionMaterials returned Success with bad input";
  }
}
