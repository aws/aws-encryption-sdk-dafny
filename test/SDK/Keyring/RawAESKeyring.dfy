include "../../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../../src/SDK/AlgorithmSuite.dfy"
include "../../../src/SDK/MessageHeader.dfy"
include "../../../src/SDK/Materials.dfy"
include "../../../src/Crypto/EncryptionSuites.dfy"
include "../../../src/Crypto/AESEncryption.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../Util/TestUtils.dfy"
include "../MessageHeader.dfy"

module TestAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import RawAESKeyringDef
  import MessageHeader
  import Materials
  import EncryptionSuites
  import AlgorithmSuite
  import UTF8
  import TestUtils
  import TestMessageHeader

  method {:test} TestOnEncryptOnDecryptGenerateDataKey()
  {
    var name :- expect UTF8.Encode("test Name");
    var namespace :- expect UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    TestMessageHeader.ExpectValidAAD(encryptionContext);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    expect |encryptionMaterialsOut.encryptedDataKeys| == 1;

    var pdk := encryptionMaterialsOut.plaintextDataKey;
    var edk := encryptionMaterialsOut.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect encryptionMaterialsOut.plaintextDataKey == pdk;
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    var name :- expect UTF8.Encode("test Name");
    var namespace :- expect UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    TestMessageHeader.ExpectValidAAD(encryptionContext);

    var pdk := seq(32, i => 0);
    var traceEntry := Materials.KeyringTraceEntry([], [], {Materials.GENERATED_DATA_KEY});
    
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey))
                                                              .WithKeys(Some(pdk), [], [traceEntry]);
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    expect |encryptionMaterialsOut.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.plaintextDataKey == Some(pdk);
  }

  method {:test} TestOnDecryptNoEDKs()
  {
    var name :- expect UTF8.Encode("test Name");
    var namespace :- expect UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(decryptionMaterialsIn, []);
    expect decryptionMaterialsOut.plaintextDataKey.None?;
  }

  method {:test} TestOnEncryptUnserializableEC()
  {
    var name :- expect UTF8.Encode("test Name");
    var namespace :- expect UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- expect UTF8.Encode("keyA");
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    TestMessageHeader.ExpectInvalidAAD(unserializableEncryptionContext);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(unserializableEncryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut := rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    expect encryptionMaterialsOut.Failure?;
  }

  method {:test} TestOnDecryptUnserializableEC()
  {
    // Set up valid EDK for decryption
    var name :- expect UTF8.Encode("test Name");
    var namespace :- expect UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- expect UTF8.Encode("keyA");
    var valA :- expect UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    expect encryptionMaterialsOut.plaintextDataKey.Some?;
    expect |encryptionMaterialsOut.encryptedDataKeys| == 1;
    var edk := encryptionMaterialsOut.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    TestMessageHeader.ExpectInvalidAAD(unserializableEncryptionContext);
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(unserializableEncryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    expect decryptionMaterialsOut.Failure?;
  }

  method {:test} TestDeserializeEDKCiphertext() {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var serializedEDKCiphertext := ciphertext + authTag;
    var encOutput := RawAESKeyringDef.DeserializeEDKCiphertext(serializedEDKCiphertext, |authTag|);

    expect encOutput.cipherText == ciphertext;
    expect encOutput.authTag == authTag;
  }

  method {:test} TestSerializeEDKCiphertext() {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var encOutput := AESEncryption.EncryptionOutput(ciphertext, authTag);
    var serializedEDKCiphertext := RawAESKeyringDef.SerializeEDKCiphertext(encOutput);

    expect serializedEDKCiphertext == ciphertext + authTag;
  }

  method generateUnserializableEncryptionContext(keyA: UTF8.ValidUTF8Bytes) returns (encCtx: Materials.EncryptionContext)
  {
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    return map[keyA:=invalidVal];
  }
}
