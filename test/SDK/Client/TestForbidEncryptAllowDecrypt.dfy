// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../src/Generated/AwsEncryptionSdk.dfy"
include "../../../src/SDK/AwsEncryptionSdk.dfy"
include "../../../src/SDK/AwsEncryptionSdkFactory.dfy"
include "../../../src/SDK/Serialize/SerializableTypes.dfy"
// include "../../../src/AwsCryptographicMaterialProviders/AlgorithmSuites.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../Util/TestUtils.dfy"

module TestForbidEncryptAllowDecrypt {
  import Aws.Crypto
  import Aws.Esdk
  import AwsEncryptionSdk
  import AwsEncryptionSdkFactory
  import SerializableTypes
  import MaterialProviders
  import MaterialProviders.AlgorithmSuites
  import TestUtils
  import UTF8
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  method {:test} ForbidEncryptAllowDecrypt()
    returns (res: Result<(), string>)
  {
    // When the commitment policy "FORBID_ENCRYPT_ALLOW_DECRYPT" is configured:
    var client :- SetupEsdkClient(Some(Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT));

    var keyring :- SetupTestKeyring();

    //= compliance/client-apis/client.txt#2.4.2.1
    //= type=test
    //# *  "03 78" MUST be the default algorithm suite
    var encryptOutputDefaultAlgSuite :- expect TryEncrypt(client, keyring, None());
    expect encryptOutputDefaultAlgSuite.algorithmSuiteId ==
      SerializableTypes.GetAlgorithmSuiteId(0x0378 as SerializableTypes.ESDKAlgorithmSuiteId);

    //= compliance/client-apis/client.txt#2.4.2.1
    //= type=test
    //# *  encrypt (encrypt.md) MUST only support algorithm suites that have
    //# a Key Commitment (../framework/algorithm-suites.md#algorithm-
    //# suites-encryption-key-derivation-settings) value of False
    var encryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while encryptAlgSuitesToCheck != {}
      decreases |encryptAlgSuitesToCheck|
    {
      var id :| id in encryptAlgSuitesToCheck;
      var suite := AlgorithmSuites.GetSuite(id);
      var res := TryEncrypt(client, keyring, Some(id));
      expect suite.commitment.None? <==> res.Success?;
      encryptAlgSuitesToCheck := encryptAlgSuitesToCheck - {id};
    }

    //= compliance/client-apis/client.txt#2.4.2.1
    //= type=test
    //# *  decrypt (decrypt.md) MUST support all algorithm suites
    var decryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while decryptAlgSuitesToCheck != {}
      decreases |decryptAlgSuitesToCheck|
    {
      var id :| id in decryptAlgSuitesToCheck;
      var res := TryDecrypt(client, keyring, id);
      expect res.Success?;
      decryptAlgSuitesToCheck := decryptAlgSuitesToCheck - {id};
    }
  }

  method {:test} RequireEncryptAllowDecrypt()
    returns (res: Result<(), string>)
  {
    // When the commitment policy "REQUIRE_ENCRYPT_ALLOW_DECRYPT" is configured:
    var client :- SetupEsdkClient(Some(Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT));

    var keyring :- SetupTestKeyring();

    //= compliance/client-apis/client.txt#2.4.2.2
    //= type=test
    //# *  "05 78" MUST be the default algorithm suite
    var encryptOutputDefaultAlgSuite :- expect TryEncrypt(client, keyring, None());
    expect encryptOutputDefaultAlgSuite.algorithmSuiteId ==
      SerializableTypes.GetAlgorithmSuiteId(0x0578 as SerializableTypes.ESDKAlgorithmSuiteId);

    //= compliance/client-apis/client.txt#2.4.2.2
    //= type=test
    //# *  encrypt (encrypt.md) MUST only support algorithm suites that have
    //# a Key Commitment (../framework/algorithm-suites.md#algorithm-
    //# suites-encryption-key-derivation-settings) value of True
    var encryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while encryptAlgSuitesToCheck != {}
      decreases |encryptAlgSuitesToCheck|
    {
      var id :| id in encryptAlgSuitesToCheck;
      var suite := AlgorithmSuites.GetSuite(id);
      var res := TryEncrypt(client, keyring, Some(id));
      expect !suite.commitment.None? <==> res.Success?;
      encryptAlgSuitesToCheck := encryptAlgSuitesToCheck - {id};
    }

    //= compliance/client-apis/client.txt#2.4.2.2
    //= type=test
    //# *  decrypt (decrypt.md) MUST support all algorithm suites
    var decryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while decryptAlgSuitesToCheck != {}
      decreases |decryptAlgSuitesToCheck|
    {
      var id :| id in decryptAlgSuitesToCheck;
      var res := TryDecrypt(client, keyring, id);
      expect res.Success?;
      decryptAlgSuitesToCheck := decryptAlgSuitesToCheck - {id};
    }
  }

  method {:test} RequireEncryptRequireDecrypt()
    returns (res: Result<(), string>)
  {
    // When the commitment policy "REQUIRE_ENCRYPT_REQUIRE_DECRYPT" is configured:
    var client :- SetupEsdkClient(Some(Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT));

    var keyring :- SetupTestKeyring();

    //= compliance/client-apis/client.txt#2.4.2.3
    //= type=test
    //# *  "05 78" MUST be the default algorithm suite
    var encryptOutputDefaultAlgSuite :- expect TryEncrypt(client, keyring, None());
    expect encryptOutputDefaultAlgSuite.algorithmSuiteId ==
      SerializableTypes.GetAlgorithmSuiteId(0x0578 as SerializableTypes.ESDKAlgorithmSuiteId);

    //= compliance/client-apis/client.txt#2.4.2.3
    //= type=test
    //# *  encrypt (encrypt.md) MUST only support algorithm suites that have
    //# a Key Commitment (../framework/algorithm-suites.md#algorithm-
    //# suites-encryption-key-derivation-settings) value of True
    var encryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while encryptAlgSuitesToCheck != {}
      decreases |encryptAlgSuitesToCheck|
    {
      var id :| id in encryptAlgSuitesToCheck;
      var suite := AlgorithmSuites.GetSuite(id);
      var res := TryEncrypt(client, keyring, Some(id));
      expect !suite.commitment.None? <==> res.Success?;
      encryptAlgSuitesToCheck := encryptAlgSuitesToCheck - {id};
    }

    //= compliance/client-apis/client.txt#2.4.2.3
    //= type=test
    //# *  decrypt (decrypt.md) MUST only support algorithm suites that have
    //# a Key Commitment (../framework/algorithm-suites.md#algorithm-
    //# suites-encryption-key-derivation-settings) value of True
    var decryptAlgSuitesToCheck := AlgorithmSuites.SupportedAlgorithmSuiteIds;
    while decryptAlgSuitesToCheck != {}
      decreases |decryptAlgSuitesToCheck|
    {
      var id :| id in decryptAlgSuitesToCheck;
      var suite := AlgorithmSuites.GetSuite(id);
      var res := TryDecrypt(client, keyring, id);
      expect !suite.commitment.None? <==> res.Success?;
      decryptAlgSuitesToCheck := decryptAlgSuitesToCheck - {id};
    }
  }

  method SetupEsdkClient(commitmentPolicy: Option<Crypto.CommitmentPolicy>)
    returns (res: Result<Esdk.IAwsEncryptionSdk, string>)
  {
    var config := Esdk.AwsEncryptionSdkConfig(
      maxEncryptedDataKeys := None(),
      commitmentPolicy := commitmentPolicy
    );
    var clientFactory := new AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();
    var client :- expect clientFactory.CreateAwsEncryptionSdk(config);
    return Success(client);
  }

  method SetupTestKeyring()
    returns (res: Result<Crypto.IKeyring, string>)
  {
    var materialsClient := new MaterialProviders.Client.AwsCryptographicMaterialProviders();
    var keyring :- expect materialsClient.CreateRawAesKeyring(Crypto.CreateRawAesKeyringInput(
      keyNamespace := "someNamespace",
      keyName := "someName",
      wrappingKey := seq(32, i => 0),
      wrappingAlg := Crypto.ALG_AES256_GCM_IV12_TAG16));
    return Success(keyring);
  }

  method TryEncrypt(
    client: Esdk.IAwsEncryptionSdk,
    keyring: Crypto.IKeyring,
    algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>
  )
    returns (res: Result<Esdk.EncryptOutput, Esdk.IAwsEncryptionSdkException>)
  {
    var input := Esdk.EncryptInput(
      plaintext := [],
      encryptionContext := None(),
      algorithmSuiteId := algorithmSuiteId,
      materialsManager := None(),
      keyring := Some(keyring),
      frameLength := None());
    var output := client.Encrypt(input);
    return output;
  }

  method TryDecrypt(
    client: Esdk.IAwsEncryptionSdk,
    keyring: Crypto.IKeyring,
    algorithmSuiteId: Crypto.AlgorithmSuiteId
  )
    returns (res: Result<Esdk.DecryptOutput, Esdk.IAwsEncryptionSdkException>)
  {
    var encryptCommitmentPolicy := if AlgorithmSuites.GetSuite(algorithmSuiteId).commitment.None?
      then Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
      else Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT;
    var encryptClient :- expect SetupEsdkClient(Some(encryptCommitmentPolicy));
    var encryptOutput :- expect TryEncrypt(encryptClient, keyring, Some(algorithmSuiteId));

    var decryptInput := Esdk.DecryptInput(
      ciphertext := encryptOutput.ciphertext,
      materialsManager := None(),
      keyring := Some(keyring));
    var decryptOutput := client.Decrypt(decryptInput);
    return decryptOutput;
  }
}
