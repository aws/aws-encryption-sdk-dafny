// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestConfig {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers

  const branchKeyStoreName := "KeyStoreTestTable";
  const logicalKeyStoreName := "KeyStoreTestTable";
  // THIS IS A TESTING RESOURCE DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
  const keyId := "9d989aa2-2f9c-438c-a745-cc57d3ad0126";

  method {:test} TestInvalidKmsKeyArnConfig() {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyId);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );
    
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Failure?;
    expect keyStore.error == Types.KeyStoreException(message := "Invalid AWS KMS Key Arn");
  }

  method {:test} TestValidConfig() {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );
    
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;
  }

  method {:test} TestValidConfigNoClients() {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    
    // Test with no kms client supplied
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := None
    );
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;

    // Test with no ddb client supplied
    keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := None,
      kmsClient := Some(kmsClient)
    );
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;
    
    // Test with no clients supplied
    keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := None,
      kmsClient := None
    );
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;
  }
}
