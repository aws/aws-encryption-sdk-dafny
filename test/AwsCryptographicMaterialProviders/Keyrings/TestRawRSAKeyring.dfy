// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/AwsCryptographicMaterialProviders/Keyrings/RawRSAKeyring.dfy"
include "../../../src/AwsCryptographicMaterialProviders/AlgorithmSuites.dfy"
include "../../../src/AwsCryptographicMaterialProviders/Materials.dfy"
include "../../../src/Crypto/RSAEncryption.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../Util/TestUtils.dfy"

module TestRawRSAKeying {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import RSAEncryption
  import MaterialProviders.RawRSAKeyring
  import EncryptionContext
  import UTF8
  import Aws.Crypto
  import opened TestUtils
  import MaterialProviders.Materials

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey, rawRSAKeyring := GenerateKeyPairAndKeyring(
      namespace,
      name,
      2048 as RSAEncryption.StrengthBits,
      RSAEncryption.PaddingMode.OAEP_SHA1
    );
    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );
    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=None()
    );
    expect Materials.ValidEncryptionMaterials(encryptionMaterialsIn);  
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(
      Crypto.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    expect Materials.ValidEncryptionMaterials(encryptionMaterialsOut.materials);  
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.None,
      verificationKey:=Option.None
    );    

    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(
      Crypto.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );
      
    //= compliance/framework/raw-rsa-keyring.txt#2.6.1
    //= type=test
    //# The keyring MUST attempt to encrypt the plaintext data key in the
    //# encryption materials (structures.md#encryption-materials) using RSA.
    // We demonstrate this by showing OnEncrypt then OnDecrypt gets us the same pdk back.
    expect decryptionMaterialsOut.materials.plaintextDataKey == Some(pdk);      
  }

  method {:test} TestOnDecryptKeyNameMismatch()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey, rawRSAKeyring := GenerateKeyPairAndKeyring(
      namespace,
      name,
      2048 as RSAEncryption.StrengthBits,
      RSAEncryption.PaddingMode.OAEP_SHA1
    );
    
    var mismatchName :- expect UTF8.Encode("mismatched");
    var mismatchedRSAKeyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      mismatchName,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      RSAEncryption.PaddingMode.OAEP_SHA1
    );

    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=Option.None
    );
    var encryptionMaterialsOut :- expect mismatchedRSAKeyring.OnEncrypt(
      Crypto.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.None,
      verificationKey:=Option.None
    );
    var decryptionMaterialsOut := rawRSAKeyring.OnDecrypt(
      Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk])
    );

    expect decryptionMaterialsOut.IsFailure();
  }

  method {:test} TestOnDecryptFailure()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var _, _, encryptKeyring := GenerateKeyPairAndKeyring(
      namespace,
      name,
      2048 as RSAEncryption.StrengthBits,
      RSAEncryption.PaddingMode.OAEP_SHA1
    );
    var _, _, decryptKeyring := GenerateKeyPairAndKeyring(
      namespace,
      name,
      2048 as RSAEncryption.StrengthBits,
      RSAEncryption.PaddingMode.OAEP_SHA1
    );  

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=Option.None
    );
    var encryptionMaterialsOut :- expect encryptKeyring.OnEncrypt(
      Crypto.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.None,
      verificationKey:=Option.None
    );
    var decryptionMaterialsOut := decryptKeyring.OnDecrypt(
      Crypto.OnDecryptInput(materials:=decryptionMaterialsIn, encryptedDataKeys:=[edk])
    );
    
    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
    //= type=test
    //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
    //# the decryption materials (structures.md#decryption-materials).
    expect decryptionMaterialsOut.IsFailure();
  }  

  // The RSA Keyring should attempt to decrypt every EDK that matches its keyname
  // and namespace, until it succeeds.
  // Here, we generate a valid EDK that the keyring should decrypt
  // and create a fake EDK that it will not be able to decrypt.
  // The keyring should fail to decrypt the fake one, and then
  // succeed with the real EDK, and return the PDK.
  method {:test} TestOnDecryptBadAndGoodEdkSucceeds()
  {
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey, rawRSAKeyring := GenerateKeyPairAndKeyring(
      namespace,
      name,
      2048 as RSAEncryption.StrengthBits,
      RSAEncryption.PaddingMode.OAEP_SHA1
    );
    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );
    var pdk := seq(32, i => 0);

    var wrappingAlgorithmID := Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF;
    var encryptionMaterialsIn := Crypto.EncryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Some(pdk),
      encryptedDataKeys:=[],
      signingKey:=None()
    );
    expect Materials.ValidEncryptionMaterials(encryptionMaterialsIn);  
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(
      Crypto.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    expect Materials.ValidEncryptionMaterials(encryptionMaterialsOut.materials);  
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn := Crypto.DecryptionMaterials(
      encryptionContext:=encryptionContext,
      algorithmSuiteId:=wrappingAlgorithmID,
      plaintextDataKey:=Option.None,
      verificationKey:=Option.None
    );    
    var fakeEdk: Crypto.EncryptedDataKey := Crypto.EncryptedDataKey(
      keyProviderId := edk.keyProviderId,
      keyProviderInfo := edk.keyProviderInfo,
      ciphertext := seq(|edk.ciphertext|, i => 0)
    );

    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
    //= type=test
    //# The keyring MUST attempt to decrypt the input encrypted data keys, in
    //# list order, until it successfully decrypts one.
    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(
      Crypto.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[fakeEdk, edk]
      )
    );
    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
    //= type=test
    //# If any decryption succeeds, this keyring MUST immediately return the
    //# input decryption materials (structures.md#decryption-materials),
    //# modified in the following ways:
    expect decryptionMaterialsOut.materials.plaintextDataKey == Some(pdk);      
  }
  
  method GenerateKeyPairAndKeyring(
    namespace: UTF8.ValidUTF8Bytes,
    name: UTF8.ValidUTF8Bytes,
    keyStrength: RSAEncryption.StrengthBits,
    padding: RSAEncryption.PaddingMode
  )
    returns (
      publicKey: RSAEncryption.PublicKey,
      privateKey: RSAEncryption.PrivateKey,
      keyring: RawRSAKeyring.RawRSAKeyring
    )
    requires |namespace| < UINT16_LIMIT
    requires |name| < UINT16_LIMIT
    requires keyStrength <= 4096
  {
    publicKey, privateKey := RSAEncryption.GenerateKeyPair(
      keyStrength
    );
    keyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      name,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      padding
    );
    return publicKey, privateKey, keyring;
  }
  
}
