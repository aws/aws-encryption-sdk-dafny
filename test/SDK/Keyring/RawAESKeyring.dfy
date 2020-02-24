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

  method {:test} TestOnEncryptOnDecryptGenerateDataKey() returns (r: Result<()>)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var isValidAAD := MessageHeader.ComputeValidAAD(encryptionContext);
    var _ :- Require(isValidAAD);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut :- rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    var _ :- Require(|encryptionMaterialsOut.encryptedDataKeys| == 1);

    var pdk := encryptionMaterialsOut.plaintextDataKey;
    var edk := encryptionMaterialsOut.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    r := Require(encryptionMaterialsOut.plaintextDataKey == pdk);
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: Result<()>)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var isValidAAD := MessageHeader.ComputeValidAAD(encryptionContext);
    var _ :- Require(isValidAAD);

    var pdk := seq(32, i => 0);
    var traceEntry := Materials.KeyringTraceEntry([], [], {Materials.GENERATED_DATA_KEY});
    
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey))
                                                              .WithKeys(Some(pdk), [], [traceEntry]);
    var encryptionMaterialsOut :- rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    var _ :- Require(|encryptionMaterialsOut.encryptedDataKeys| == 1);

    var edk := encryptionMaterialsOut.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    r := Require(decryptionMaterialsOut.plaintextDataKey == Some(pdk));
  }

  method {:test} TestOnDecryptNoEDKs() returns (r: Result<()>)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(encryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut :- rawAESKeyring.OnDecrypt(decryptionMaterialsIn, []);
    r := Require(decryptionMaterialsOut.plaintextDataKey.None?);
  }

  method {:test} TestOnEncryptUnserializableEC() returns (r: Result<()>)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    var isValidAAD := MessageHeader.ComputeValidAAD(unserializableEncryptionContext);
    var _ :- Require(!isValidAAD);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(unserializableEncryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut := rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    r := Require(encryptionMaterialsOut.Failure?);
  }

  method {:test} TestOnDecryptUnserializableEC() returns (r: Result<()>)
  {
    // Set up valid EDK for decryption
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := map[keyA := valA];
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Materials.EncryptionMaterials.WithoutDataKeys(encryptionContext, wrappingAlgorithmID, Some(signingKey));
    var encryptionMaterialsOut :- rawAESKeyring.OnEncrypt(encryptionMaterialsIn);
    var _ :- Require(encryptionMaterialsOut.plaintextDataKey.Some?);
    var _ :- Require(|encryptionMaterialsOut.encryptedDataKeys| == 1);
    var edk := encryptionMaterialsOut.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    var isValidAAD := MessageHeader.ComputeValidAAD(unserializableEncryptionContext);
    var _ :- Require(!isValidAAD);
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Materials.DecryptionMaterials.WithoutPlaintextDataKey(unserializableEncryptionContext, wrappingAlgorithmID, Some(verificationKey));
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(decryptionMaterialsIn, [edk]);
    r := Require(decryptionMaterialsOut.Failure?);
  }

  method {:test} TestDeserializeEDKCiphertext() returns (r: Result<()>) {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var serializedEDKCiphertext := ciphertext + authTag;
    var encOutput := RawAESKeyringDef.DeserializeEDKCiphertext(serializedEDKCiphertext, |authTag|);

    var _ :- RequireEqual(encOutput.cipherText, ciphertext);
    r := RequireEqual(encOutput.authTag, authTag);
  }

  method {:test} TestSerializeEDKCiphertext() returns (r: Result<()>) {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var encOutput := AESEncryption.EncryptionOutput(ciphertext, authTag);
    var serializedEDKCiphertext := RawAESKeyringDef.SerializeEDKCiphertext(encOutput);

    r := RequireEqual(serializedEDKCiphertext, ciphertext + authTag);
  }

  method generateUnserializableEncryptionContext(keyA: UTF8.ValidUTF8Bytes) returns (encCtx: Materials.EncryptionContext)
  {
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    return map[keyA:=invalidVal];
  }
}
