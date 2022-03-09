// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../src/Generated/AwsEncryptionSdk.dfy"
include "../../src/AwsCryptographicMaterialProviders/Client.dfy"
include "../../src/SDK/AwsEncryptionSdkFactoryClient.dfy"
include "../../src/SDK/AwsEncryptionSdk.dfy"
include "../../src/Crypto/RSAEncryption.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"
include "../Util/TestUtils.dfy"

module {:extern "TestClient"} TestClient {
  import Aws.Esdk
  import Aws.Crypto
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened StandardLibrary
  import Base64
  import MaterialProviders.Client
  import AwsEncryptionSdk
  import AwsEncryptionSdkFactoryClient

  import UTF8

  import TestUtils

  method {:test} HappyPath()
  {
    // Create material provider client
    var materialsClient := new Client.AwsCryptographicMaterialProvidersClient();

    // Use material provider client API for RawAESKeyring creation
    var rawAESKeyringResult := materialsClient.CreateRawAesKeyring(Crypto.CreateRawAesKeyringInput(
      keyNamespace := "someNamespace",
      keyName := "someName",
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Crypto.ALG_AES256_GCM_IV12_TAG16));
    expect rawAESKeyringResult.Success?;
    var rawAESKeyring := rawAESKeyringResult.value;

    // Use material provider client API for DefaultCMM creation
    var cmmResult := materialsClient.CreateDefaultCryptographicMaterialsManager(Crypto.CreateDefaultCryptographicMaterialsManagerInput(
      keyring := rawAESKeyring
    ));
    expect cmmResult.Success?;
    var cmm := cmmResult.value;

    // Create AWS Crypto client
    var config := Esdk.AwsEncryptionSdkClientConfig(
      configDefaults := Esdk.V1,
      maxEncryptedDataKeys := Option.Some(2 as int64),
      commitmentPolicy := Option.Some(Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT) // TODO: update once commitment algs working
    );
    // TODO This is a bit wordy here, but ideally the language specific compilers can translate this to something that is
    // a better user experience
    var clientFactory := new AwsEncryptionSdkFactoryClient.AwsEncryptionSdkFactoryClient();
    var clientResult := clientFactory.MakeAwsEncryptionSdk(config);
    expect clientResult.Success?;
    var client := clientResult.value;

    // Use Encrypt API
    var plaintext :- expect UTF8.Encode("hello");
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var input := Esdk.EncryptInput(
      plaintext:=plaintext,
      encryptionContext:=Some(encryptionContext),
      algorithmSuiteId:=None(),
      materialsManager:=Some(cmm),
      keyring:=None(),
      frameLength:=Option.None());
    var res :- expect client.Encrypt(input);

    // Use Decrypt API
    var decryptInput := Esdk.DecryptInput(ciphertext:=res.ciphertext, materialsManager:=Some(cmm), keyring:=None());
    var d :- expect client.Decrypt(decryptInput);

    // ensure expected output
    expect plaintext == d.plaintext;
  }
}
