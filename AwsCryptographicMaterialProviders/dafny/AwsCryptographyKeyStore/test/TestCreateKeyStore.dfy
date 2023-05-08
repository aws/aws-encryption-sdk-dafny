// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"

module TestCreateKeyStore {
  import Types = AwsCryptographyKeyStoreTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers
  import opened AwsArnParsing

  const keyStoreName := "KeyStoreTestTable";

  // TODO Figure out how to run this in ci
  // method {:test} TestCreateKeyStore()
  // {
  //   var kmsClient :- expect KMS.KMSClient();
  //   var ddbClient :- expect DDB.DynamoDBClient();
  //   var keyStoreConfig := Types.KeyStoreConfig(
  //     ddbTableName := Some(keyStoreName),
  //     ddbClient := Some(ddbClient),
  //     kmsClient := Some(kmsClient)
  //   );

  //   var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
  //   var keyStoreArn :- expect keyStore.CreateKeyStore(Types.CreateKeyStoreInput());
    
  //   expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).Success?;
  //   expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).value == keyStoreName;
  // }
}
