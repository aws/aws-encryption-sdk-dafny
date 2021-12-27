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
    var keyStrength: RSAEncryption.StrengthBits := 2048;
    var padding: RSAEncryption.PaddingMode := RSAEncryption.PaddingMode.OAEP_SHA1;
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey := RSAEncryption.GenerateKeyPair(
      keyStrength,
      padding
    );
    var rawRSAKeyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      name,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      padding
    );
    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );
    var pdk := seq(32, i => 0);

    // QUESTION :: What does a wrappingAlgorithmID do for an RSA Keyring?
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
    var keyStrength: RSAEncryption.StrengthBits := 2048;
    var padding: RSAEncryption.PaddingMode := RSAEncryption.PaddingMode.OAEP_SHA1;
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey := RSAEncryption.GenerateKeyPair(
      keyStrength,
      padding
    );
    var rawRSAKeyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      name,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      padding
    );
    var mismatchName :- expect UTF8.Encode("mismatched");
    var mismatchedRSAKeyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      mismatchName,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      padding
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
    var keyStrength: RSAEncryption.StrengthBits := 2048;
    var padding: RSAEncryption.PaddingMode := RSAEncryption.PaddingMode.OAEP_SHA1;
    var namespace, name := TestUtils.NamespaceAndName(0);
    var publicKey, privateKey := RSAEncryption.GenerateKeyPair(keyStrength, padding);
    var encryptKeying := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      name,
      Option.Some(publicKey.pem),
      Option.Some(privateKey.pem),
      padding
    );
    var publicKeyToFail, privateKeyToFail := RSAEncryption.GenerateKeyPair(keyStrength, padding);      
    var decryptKeyring := new RawRSAKeyring.RawRSAKeyring(
      namespace,
      name,
      Option.Some(publicKeyToFail.pem),
      Option.Some(privateKeyToFail.pem),
      padding
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
    var encryptionMaterialsOut :- expect encryptKeying.OnEncrypt(
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
  
}
