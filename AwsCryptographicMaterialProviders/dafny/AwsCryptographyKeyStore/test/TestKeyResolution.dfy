// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/CreateKeys.dfy"
include "../src/KeyResolution.dfy"

module TestKeyResolution {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import DDBTypes = ComAmazonawsDynamodbTypes
  import KMSTypes = ComAmazonawsKmsTypes
  import KeyStore
  import UUID
  import Time
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsKmsUtils
  import opened CreateKeys
  import opened KeyResolution
  
  const branchKeyStoreName := "KeyStoreTestTable";
  // THESE ARE TESTING RESOURCES DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";

  method {:test} TestActiveBranchKeyResolution() {
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

    // Create a new key
    // We will create a use this new key per run to avoid tripping up
    // when running in different runtimes across different hosts
    var branchKeyIdentifier :- expect keyStore.CreateKey();
    
    WriteActiveActiveBranchKey(branchKeyIdentifier.branchKeyIdentifier, kmsClient, ddbClient);

    // Resolve active key to latest key based on lexicographically timestamp value
    var resolveActiveKeyResult := keyStore.BranchKeyStatusResolution(Types.BranchKeyStatusResolutionInput(
      branchKeyIdentifier := branchKeyIdentifier.branchKeyIdentifier
    ));

    expect resolveActiveKeyResult.Success?;
  }

  method WriteActiveActiveBranchKey(branchKeyIdentifer: string, kmsClient: KMSTypes.IKMSClient, ddbClient: DDBTypes.IDynamoDBClient) 
    requires kmsClient.ValidState() && ddbClient.ValidState()
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {

    // DO NOT use the KeyStore methods this way
    // We are doing this in order to continuously test that the APIs work
    // as spec'd out.
    
    // In order to be able to test this again in ci we will deliberately
    // add another active key under this branch key id
    var timestamp := Time.GetCurrentTimeStamp();
    var version := UUID.GenerateUUID();
    expect timestamp.Success? && version.Success?;

    var activeActiveBranchKeyEncryptionContext := activeBranchKeyEncryptionContext(
      branchKeyIdentifer,
      version.value,
      timestamp.value,
      branchKeyStoreName,
      keyArn
    );

    var grantTokens := GetValidGrantTokens(None);
    var maybeActiveActiveBranchKeyWithoutPlaintext := GenerateKey(
      activeActiveBranchKeyEncryptionContext,
      keyArn,
      grantTokens.value,
      kmsClient
    );

    expect maybeActiveActiveBranchKeyWithoutPlaintext.Success?;
    var activeActiveBranchKeyWithoutPlaintext := maybeActiveActiveBranchKeyWithoutPlaintext.value;

    expect activeActiveBranchKeyWithoutPlaintext.CiphertextBlob.Some?;
    var activeActiveBranchKeyDDBMap := ToBranchKeyItemAttributeMap(
      activeActiveBranchKeyEncryptionContext,
      activeActiveBranchKeyWithoutPlaintext.CiphertextBlob.value
    );

    var writeActiveActiveBranchKey := WriteDecryptOnlyBranchKeys(
      [activeActiveBranchKeyDDBMap],
      branchKeyStoreName,
      ddbClient
    );

    expect writeActiveActiveBranchKey.Success?;
  }
}
