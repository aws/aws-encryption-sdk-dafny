// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/AwsCryptographicMaterialProviders/Keyrings/RawAESKeyring.dfy"
include "../../../src/AwsCryptographicMaterialProviders/AlgorithmSuites.dfy"
include "../../../src/AwsCryptographicMaterialProviders/Materials.dfy"
include "../../../src/Crypto/AESEncryption.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../Util/TestUtils.dfy"

module TestAESKeyring {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AESEncryption
  import MaterialProviders.RawAESKeyring
  import MessageHeader
  import MaterialProviders.Materials
  import EncryptionContext
  import AlgorithmSuite
  import UTF8
  import Aws.Crypto
  import opened TestUtils

  method {:test} TestOnEncryptOnDecryptGenerateDataKey()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    ExpectSerializableEncryptionContext(encryptionContext);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      encryptedDataKeys:=[],
      signingKey:=Some(signingKey)
    );
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Crypto.OnEncryptInput(materials:=encryptionMaterialsIn));

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# The keyring MUST append the constructed encrypted data key to the
    //# encrypted data key list in the encryption materials
    //# (structures.md#encryption-materials).

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# OnEncrypt MUST output the modified encryption materials
    //# (structures.md#encryption-materials).
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var pdk := encryptionMaterialsOut.materials.plaintextDataKey;
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      verificationKey:=Some(verificationKey)
    );
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk]));

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=test
    //# If a decryption succeeds, this keyring MUST add the resulting
    //# plaintext data key to the decryption materials and return the
    //# modified materials.
    expect encryptionMaterialsOut.materials.plaintextDataKey == pdk;
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    ExpectSerializableEncryptionContext(encryptionContext);

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=Some(signingKey)
    );
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Crypto.OnEncryptInput(materials:=encryptionMaterialsIn));
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      verificationKey:=Some(verificationKey)
    );
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk]));

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# The keyring MUST encrypt the plaintext data key in the encryption
    //# materials (structures.md#encryption-materials) using AES-GCM.
    // We demonstrate this by showing OnEncrypt then OnDecrypt gets us the same pdk back.
    expect decryptionMaterialsOut.materials.plaintextDataKey == Some(pdk);
  }

    method {:test} TestOnDecryptKeyNameMismatch()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));

    var mismatchName :- expect UTF8.Encode("mismatched");
    var mismatchedAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      mismatchName,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    ExpectSerializableEncryptionContext(encryptionContext);

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=Some(signingKey)
    );
    var encryptionMaterialsOut :- expect mismatchedAESKeyring.OnEncrypt(Crypto.OnEncryptInput(materials:=encryptionMaterialsIn));
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      verificationKey:=Some(verificationKey)
    );
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk]));
    expect decryptionMaterialsOut.materials.plaintextDataKey.None?;
  }

  // TODO test for multiple EDKS for OnDecrypt
  // TODO possibly test failure for one?
  // or is it easier to verify this...

  // TODO test with EDK that shouldn't be decrypted, so with another Keyring e.g.

  //= compliance/framework/raw-aes-keyring.txt#2.7.1
  //= type=test
  //# If the encryption materials (structures.md#encryption-materials) do
  //# not contain a plaintext data key, OnEncrypt MUST generate a random
  //# plaintext data key and set it on the encryption materials
  //# (structures.md#encryption-materials).
  method {:test} TestOnDecryptNoEDKs()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));
    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var verificationKey := seq(32, i => 0);
    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      verificationKey:=Some(verificationKey)
    );
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[]));
    expect decryptionMaterialsOut.materials.plaintextDataKey.None?;
  }

  //= compliance/framework/raw-aes-keyring.txt#2.7.1
  //= type=test
  //# The keyring MUST attempt to serialize the encryption materials'
  //# (structures.md#encryption-materials) encryption context
  //# (structures.md#encryption-context-1) in the same format as the
  //# serialization of message header AAD key value pairs (../data-format/
  //# message-header.md#key-value-pairs).

  method {:test} TestOnEncryptUnserializableEC()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();
    ExpectNonSerializableEncryptionContext(unserializableEncryptionContext);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
        var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=unserializableEncryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      encryptedDataKeys:=[],
      signingKey:=Some(signingKey)
    );
    var encryptionMaterialsOut := rawAESKeyring.OnEncrypt(Crypto.OnEncryptInput(materials:=encryptionMaterialsIn));
    expect encryptionMaterialsOut.Failure?;
  }

  //= compliance/framework/raw-aes-keyring.txt#2.7.2
  //= type=test
  //# The keyring MUST attempt to serialize the decryption materials'
  //# (structures.md#decryption-materials) encryption context
  //# (structures.md#encryption-context-1) in the same format as the
  //# serialization of the message header AAD key value pairs (../data-
  //# format/message-header.md#key-value-pairs).
  method {:test} TestOnDecryptUnserializableEC()
  {
    // Set up valid EDK for decryption
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring := new RawAESKeyring.RawAESKeyring(
      namespace,
      name,
      seq(32, i => 0),
      AESEncryption.AES_GCM(
        keyLength := 32 as AESEncryption.KeyLength,
        tagLength := 16 as AESEncryption.TagLength,
        ivLength := 12 as AESEncryption.IVLength
      ));
    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    var signingKey := seq(32, i => 0);
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      encryptedDataKeys:=[],
      signingKey:=Some(signingKey)
    );
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Crypto.OnEncryptInput(materials:=encryptionMaterialsIn));
    expect encryptionMaterialsOut.materials.plaintextDataKey.Some?;
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();
    ExpectNonSerializableEncryptionContext(unserializableEncryptionContext);
    var verificationKey := seq(32, i => 0);

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=unserializableEncryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=None(),
      verificationKey:=Some(verificationKey)
    );
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk]));
    expect decryptionMaterialsOut.Failure?;
  }

  method {:test} TestDeserializeEDKCiphertext() {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var serializedEDKCiphertext := ciphertext + authTag;
    var encOutput := RawAESKeyring.DeserializeEDKCiphertext(serializedEDKCiphertext, |authTag|);

    expect encOutput.cipherText == ciphertext;
    expect encOutput.authTag == authTag;
  }

  method {:test} TestSerializeEDKCiphertext() {
    var ciphertext := [0, 1, 2, 3];
    var authTag := [4, 5, 6, 7];
    var encOutput := AESEncryption.EncryptionOutput(ciphertext, authTag);
    var serializedEDKCiphertext := RawAESKeyring.SerializeEDKCiphertext(encOutput);

    expect serializedEDKCiphertext == ciphertext + authTag;
  }

  method generateUnserializableEncryptionContext() returns (encCtx: EncryptionContext.Map)
  {
    var keyA :- expect UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    AssumeLongSeqIsValidUTF8(invalidVal);
    return map[keyA:=invalidVal];
  }
}
