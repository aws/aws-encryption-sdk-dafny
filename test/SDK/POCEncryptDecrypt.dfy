// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Keyring/RawAESKeyring.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../src/Generated/AwsEncryptionSdk.dfy"
include "../../src/SDK/AwsCryptographicMaterialProviders.dfy"
include "../../src/SDK/AwsEncryptionSdk.dfy"
include "../../src/SDK/EncryptionContext.dfy"
include "../../src/Crypto/RSAEncryption.dfy"
include "../../src/Crypto/EncryptionSuites.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"
include "../Util/TestUtils.dfy"


module {:extern "TestClient"} TestClient {
  import Aws.Esdk
  import Aws.Crypto
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened StandardLibrary
  import RawAESKeyringDef
  import EncryptionSuites
  import Base64
  import AwsCryptographicMaterialProviders
  import AwsEncryptionSdk

  import UTF8

  import TestUtils

  method {:test} HappyPath() 
  {
    // Create material provider client
    var materialsClient := new AwsCryptographicMaterialProviders.AwsCryptographicMaterialProvidersClient();

    // Use material provider client API for RawAESKeyring creation
    var rawAESKeyring := materialsClient.CreateRawAesKeyring(Crypto.CreateRawAesKeyringInput(
      keyNamespace := "someNamespace",
      keyName := "someName",
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Crypto.ALG_AES256_GCM_IV12_TAG16));

    // Use material provider client API for DefaultCMM creation
    var cmm := materialsClient.CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
      keyring := rawAESKeyring
    ));

    // Create AWS Crypto client
    // TODO use createClient
    var client := new AwsEncryptionSdk.AwsEncryptionSdkClient(Esdk.ConfigurationDefaults.V1);

    // Use Encrypt API
    var plaintext :- expect UTF8.Encode("hello");
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var input := Esdk.EncryptInput(
      plaintext:=plaintext,
      encryptionContext:=encryptionContext,
      algorithmSuiteID:=None(),
      materialsManager:=cmm);
    var res :- expect client.Encrypt(input);

    // Use Decrypt API
    var decryptInput := Esdk.DecryptInput(ciphertext:=res.ciphertext, materialsManager:=cmm);
    var d :- expect client.Decrypt(decryptInput);

    // ensure expected output
    expect plaintext == d.plaintext;
  }
}
