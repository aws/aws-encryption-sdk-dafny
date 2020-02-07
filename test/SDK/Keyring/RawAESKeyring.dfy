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

  method {:test} TestOnEncryptOnDecryptGenerateDataKey() returns (r: TestResult)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    var isValidAAD := MessageHeader.ComputeValidAAD(encryptionContext);
    :- Require(isValidAAD);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;

    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, None);
    :- Require(onEncryptResult.Some? && |onEncryptResult.get.encryptedDataKeys| == 1);

    var pdk := onEncryptResult.get.plaintextDataKey;
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey() returns (r: TestResult)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    var isValidAAD := MessageHeader.ComputeValidAAD(encryptionContext);
    :- Require(isValidAAD);

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;

    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, Some(pdk));
    :- Require(onEncryptResult.Some? && |onEncryptResult.get.encryptedDataKeys| == 1);

    var edk := onEncryptResult.get.encryptedDataKeys[0];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, [edk]);
    r := Require(res.Some? && res.get.plaintextDataKey == pdk);
  }

  method {:test} TestOnDecryptNoEDKs() returns (r: TestResult)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];

    var res :- rawAESKeyring.OnDecrypt(wrappingAlgorithmID, encryptionContext, []);
    r := Require(res.None?);
  }

  method {:test} TestOnEncryptUnserializableEC() returns (r: TestResult)
  {
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    var isValidAAD := MessageHeader.ComputeValidAAD(unserializableEncryptionContext);
    :- Require(!isValidAAD);

    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var onEncryptResult := rawAESKeyring.OnEncrypt(wrappingAlgorithmID, unserializableEncryptionContext, None);
    r := Require(onEncryptResult.Failure?);
  }

  method {:test} TestOnDecryptUnserializableEC() returns (r: TestResult)
  {
    // Set up valid EDK for decryption
    var name :- UTF8.Encode("test Name");
    var namespace :- UTF8.Encode("test Namespace");
    var rawAESKeyring := new RawAESKeyringDef.RawAESKeyring(name, namespace, seq(32, i => 0), EncryptionSuites.AES_GCM_256);
    var keyA :- UTF8.Encode("keyA");
    var valA :- UTF8.Encode("valA");
    var encryptionContext := [(keyA, valA)];
    var wrappingAlgorithmID := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var onEncryptResult :- rawAESKeyring.OnEncrypt(wrappingAlgorithmID, encryptionContext, None);
    :- Require(onEncryptResult.Some?);
    :- Require(|onEncryptResult.get.encryptedDataKeys| == 1);
    var edk := onEncryptResult.get.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := generateUnserializableEncryptionContext(keyA);
    var isValidAAD := MessageHeader.ComputeValidAAD(unserializableEncryptionContext);
    :- Require(!isValidAAD);

    var onDecryptResult := rawAESKeyring.OnDecrypt(wrappingAlgorithmID, unserializableEncryptionContext, [edk]);
    r := Require(onDecryptResult.Failure?);
  }

  method {:test} TestDeserializeEDKCiphertext() returns (r: TestResult) {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var serializedEDKCiphertext := ciphertext + authTag;
    var encOutput := RawAESKeyringDef.DeserializeEDKCiphertext(serializedEDKCiphertext, |authTag|);

    :- RequireEqual(encOutput.cipherText, ciphertext);
    r := RequireEqual(encOutput.authTag, authTag);
  }

  method {:test} TestSerializeEDKCiphertext() returns (r: TestResult) {
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
    return [(keyA, invalidVal)];
  }
}
