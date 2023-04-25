// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestCreateKeys {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers

  const branchKeyStoreName := "KeyStoreTestTable";
  // THIS IS A TESTING RESOURCE DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";

  method {:test} TestCreateBranchAndBeaconKeys()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsKeyArn := keyArn,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );
    
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    var branchKeyId :- expect keyStore.CreateKey();

    var beaconKeyResult :- expect keyStore.GetBeaconKey(Types.GetBeaconKeyInput(
      branchKeyIdentifier := branchKeyId.branchKeyIdentifier
    ));
    
    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(
      branchKeyIdentifier := branchKeyId.branchKeyIdentifier
    ));
    
    expect |beaconKeyResult.beaconKey| == 32;
    expect |activeResult.branchKey| == 32;
  }
}
