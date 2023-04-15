// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestGetBeaconKey {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers

  const branchKeyStoreName := "KeyStoreTestTable";
  const branchKeyId := "ef31c535-7436-406e-be37-371aea99b298";
  // THIS IS A TESTING RESOURCE DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
  
  method {:test} TestGetBeaconKey() 
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      ddbTableName := Some(branchKeyStoreName),
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    var beaconKeyResult :- expect keyStore.GetBeaconKey(Types.GetBeaconKeyInput(
      branchKeyIdentifier := branchKeyId,
      awsKmsKeyArn := Some(keyArn),
      grantTokens := None
    ));
    expect |beaconKeyResult.beaconKey| == 32;
  }

  method {:test} TestGetActiveKey()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      ddbTableName := Some(branchKeyStoreName),
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(
      branchKeyIdentifier := branchKeyId,
      awsKmsKeyArn := Some(keyArn),
      grantTokens := None
    ));
    
    expect |activeResult.branchKey| == 32;
  }
}