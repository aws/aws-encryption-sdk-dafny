// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/Index.dfy"
include "../TestUtils.dfy"

module TestRawAESKeyring {
  import opened Wrappers
  import TestUtils
  import UTF8
  import Aws.Cryptography.Primitives
  import AwsCryptographyPrimitivesTypes
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes

  method {:test} TestOnEncryptOnDecryptGenerateDataKey()
  {

    ghost var asdf := "asdf";

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
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

    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# If the encryption materials (structures.md#encryption-materials) do
    //# not contain a plaintext data key, OnEncrypt MUST generate a random
    //# plaintext data key and set it on the encryption materials
    //# (structures.md#encryption-materials).
    
    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# OnEncrypt MUST output the modified encryption materials
    //# (structures.md#encryption-materials).
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# The keyring MUST append the constructed encrypted data key to the
    //# encrypted data key list in the encryption materials
    //# (structures.md#encryption-materials).
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=test
    //# If a decryption succeeds, this keyring MUST add the resulting
    //# plaintext data key to the decryption materials and return the
    //# modified materials.
    expect encryptionMaterialsOut.materials.plaintextDataKey
    == encryptionMaterialsOut.materials.plaintextDataKey;
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    
    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
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

    // Adding a specific `pdk`
    // to test that the keyring
    // will encrypt it
    // as opposed to generate new plaintext data key.
    var pdk := seq(32, i => 0);
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn.( plaintextDataKey := Some(pdk) ))
    );

    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=test
    //# The keyring MUST encrypt the plaintext data key in the encryption
    //# materials (structures.md#encryption-materials) using AES-GCM.
    // We demonstrate this by showing OnEncrypt then OnDecrypt gets us the same pdk back.
    expect decryptionMaterialsOut.materials.plaintextDataKey == Some(pdk);
  }

  method {:test} TestOnDecryptKeyNameMismatch()
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
    ));

    var mismatchedAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := "mismatched",
      wrappingKey := seq(32, i => 1 ),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
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

    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(
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
    var decryptionMaterialsOut := mismatchedAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );
    expect decryptionMaterialsOut.IsFailure();
  }

  method {:test} TestOnDecryptBadAndGoodEdkSucceeds()
  {

    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
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

    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(
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
    var fakeEdk: Types.EncryptedDataKey := Types.EncryptedDataKey(
      keyProviderId := edk.keyProviderId,
      keyProviderInfo := edk.keyProviderInfo,
      ciphertext := seq(|edk.ciphertext|, i => 0)
    );

    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[fakeEdk, edk]
      )
    );

    expect decryptionMaterialsOut.materials.plaintextDataKey
    == encryptionMaterialsOut.materials.plaintextDataKey;
  }

  method {:test} TestOnDecryptNoEDKs()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
    ));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
      )
    );
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[]
      )
    );
    expect decryptionMaterialsOut.IsFailure();
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
    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
    ));
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := unserializableEncryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );
    var encryptionMaterialsOut := rawAESKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
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
    var mpl :- expect MaterialProviders.MaterialProviders();

    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(
      keyNamespace := namespace,
      keyName := name,
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16
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

    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    // Set up EC that can't be serialized
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := unserializableEncryptionContext
      )
    );
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );
    expect decryptionMaterialsOut.Failure?;
  }

  method generateUnserializableEncryptionContext() returns (encCtx: Types.EncryptionContext)
  {
    var keyA :- expect UTF8.Encode("keyA");
    var invalidVal := seq(0x1_0000, _ => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    return map[keyA:=invalidVal];
  }
}
