// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/Index.dfy"
include "../TestUtils.dfy"

module TestRawRSAKeying {
  import opened Wrappers
  import TestUtils
  import Aws.Cryptography.Primitives
  import AwsCryptographyPrimitivesTypes
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAStrengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(keys.publicKey.pem),
      privateKey := Option.Some(keys.privateKey.pem)
    ));

    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );

    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );

    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    //= compliance/framework/raw-rsa-keyring.txt#2.6.1
    //= type=test
    //# The keyring MUST attempt to encrypt the plaintext data key in the
    //# encryption materials (structures.md#encryption-materials) using RSA.
    // We demonstrate this by showing OnEncrypt then OnDecrypt gets us the same pdk back.
    expect decryptionMaterialsOut.materials.plaintextDataKey
    == encryptionMaterialsOut.materials.plaintextDataKey;
  }

  method {:test} TestOnDecryptKeyNameMismatch()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAStrengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(keys.publicKey.pem),
      privateKey := Option.Some(keys.privateKey.pem)
    ));

    var mismatchedRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := "mismatched",
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(keys.publicKey.pem),
      privateKey := Option.Some(keys.privateKey.pem)
    ));

    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    var decryptionMaterialsOut := mismatchedRSAKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    expect decryptionMaterialsOut.IsFailure();
  }

  method {:test} TestOnDecryptFailure()
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);

    // The keys are different, so the decrypt will fail
    var encryptKeys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAStrengthBits);
    var decryptKeys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAStrengthBits);

    var encryptKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(encryptKeys.publicKey.pem),
      privateKey := Option.Some(encryptKeys.privateKey.pem)
    ));

    var decryptKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(decryptKeys.publicKey.pem),
      privateKey := Option.Some(decryptKeys.privateKey.pem)
    ));

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );
    var encryptionMaterialsOut :- expect encryptKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    var decryptionMaterialsOut := decryptKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
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

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAStrengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1,
      publicKey := Option.Some(keys.publicKey.pem),
      privateKey := Option.Some(keys.privateKey.pem)
    ));

    var encryptionContext := TestUtils.SmallEncryptionContext(
      TestUtils.SmallEncryptionContextVariation.A
    );

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    var fakeEdk := Types.EncryptedDataKey(
      keyProviderId := edk.keyProviderId,
      keyProviderInfo := edk.keyProviderInfo,
      ciphertext := seq(|edk.ciphertext|, i => 0)
    );

    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
    //= type=test
    //# The keyring MUST attempt to decrypt the input encrypted data keys, in
    //# list order, until it successfully decrypts one.
    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[fakeEdk, edk]
      )
    );
    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
    //= type=test
    //# If any decryption succeeds, this keyring MUST immediately return the
    //# input decryption materials (structures.md#decryption-materials),
    //# modified in the following ways:
    expect decryptionMaterialsOut.materials.plaintextDataKey
    == encryptionMaterialsOut.materials.plaintextDataKey;
  }

  method GenerateKeyPair( keyStrength: AwsCryptographyPrimitivesTypes.RSAStrengthBits )
    returns (keys: AwsCryptographyPrimitivesTypes.GenerateRSAKeyPairOutput)
  {
    var crypto :- expect Primitives.AtomicPrimitives();

    keys :- expect crypto.GenerateRSAKeyPair(
      AwsCryptographyPrimitivesTypes.GenerateRSAKeyPairInput(
        strength := keyStrength
      )
    );
  }

}
