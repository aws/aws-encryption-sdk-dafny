// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../src/Generated/AwsEncryptionSdk.dfy"
include "../../src/AwsCryptographicMaterialProviders/Client.dfy"
include "../../src/SDK/AwsEncryptionSdkFactory.dfy"
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
  import AwsEncryptionSdkFactory

  import UTF8

  import TestUtils

  method {:test} HappyPath()
  {
    // Create material provider client
    var materialsClient := new Client.AwsCryptographicMaterialProviders();

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

    var config := Esdk.AwsEncryptionSdkConfig(
                    maxEncryptedDataKeys := Option.Some(2 as int64),
                    commitmentPolicy := Option.Some(Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT)
                  );
    var clientFactory := new AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();
    var clientResult := clientFactory.CreateAwsEncryptionSdk(config);
    expect clientResult.Success?;
    var client := clientResult.value;

    // Use Encrypt API
    var plaintext :- expect UTF8.Encode("hello");
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var input := Esdk.EncryptInput(
                   plaintext := plaintext,
                   encryptionContext := Some(encryptionContext),
                   algorithmSuiteId := Some(Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384),
                   materialsManager := Some(cmm),
                   keyring := None(),
                   frameLength := Option.None());
    var encryptRes :- expect client.Encrypt(input);

    //= compliance/client-apis/encrypt.txt#2.5
    //= type=test
    //# This behavior MUST output the following if the behavior is
    //# successful:
    var ciphertext := encryptRes.ciphertext;
    expect encryptionContext.Items <= encryptRes.encryptionContext.Items;

    //= compliance/client-apis/encrypt.txt#2.4.5
    //= type=test
    //# The algorithm suite (../framework/algorithm-suite.md) that SHOULD be
    //# used for encryption.
    expect encryptRes.algorithmSuiteId == Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;

    // Use Decrypt API
    var decryptInput := Esdk.DecryptInput(
                          ciphertext := encryptRes.ciphertext,
                          materialsManager := Some(cmm),
                          keyring := None());
    var decryptRes :- expect client.Decrypt(decryptInput);

    // ensure expected output
    expect plaintext == decryptRes.plaintext;
  }
}
