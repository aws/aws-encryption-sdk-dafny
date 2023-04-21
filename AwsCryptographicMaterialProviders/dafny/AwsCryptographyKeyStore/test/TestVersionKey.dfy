// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestVersionKey {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import UUID
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsKmsUtils

  const branchKeyStoreName := "KeyStoreTestTable";
  // THESE ARE TESTING RESOURCES DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
  
  method {:test} TestVersionKey() 
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsKeyArn := keyArn,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    // Create a new key
    // We will create a use this new key per run to avoid tripping up
    // when running in different runtimes
    var branchKeyIdentifier :- expect keyStore.CreateKey(Types.CreateKeyInput(
      grantTokens := None
    ));

    var oldActiveResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(
      branchKeyIdentifier := branchKeyIdentifier.branchKeyIdentifier,
      grantTokens := None
    ));

    var oldActiveVersion :- expect UTF8.Decode(oldActiveResult.branchKeyVersion).MapFailure(WrapStringToError);
    
    var versionKeyResult := keyStore.VersionKey(Types.VersionKeyInput(
      branchKeyIdentifier := branchKeyIdentifier.branchKeyIdentifier,
      grantTokens := None
    ));

    expect versionKeyResult.Success?;
    
    var getBranchKeyVersionResult :- expect keyStore.GetBranchKeyVersion(
      Types.GetBranchKeyVersionInput(
        branchKeyIdentifier := branchKeyIdentifier.branchKeyIdentifier,
        // We get the old active key by using the version
        branchKeyVersion := oldActiveVersion,
        grantTokens := None
      )
    );
    
    var newActiveResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(
      branchKeyIdentifier := branchKeyIdentifier.branchKeyIdentifier,
      grantTokens := None
    ));

    // We expect that getting the old active key has the same version as getting a branch key through the get version key api
    expect getBranchKeyVersionResult.branchKeyVersion == oldActiveResult.branchKeyVersion;
    // We expect that if we rotate the branch key, the returned materials MUST not be equal to the previous active key.
    expect getBranchKeyVersionResult.branchKeyVersion != newActiveResult.branchKeyVersion;
    expect getBranchKeyVersionResult.branchKey != newActiveResult.branchKey;
  }

  method {:test} TestErrorActiveActiveVersion() {
    // THIS IS THE DESIGNATED ACTIVE-ACTIVE KEY USED IN CI
    var keyId := "9dfb8978-5696-4132-a7c6-30e40fcced5a";

    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsKeyArn := keyArn,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    // First we test that if we try to version or "rotate" a branch key in an 
    // active-active situation we end up with a failure.
    var versionKeyResult := keyStore.VersionKey(Types.VersionKeyInput(
      branchKeyIdentifier := keyId,
      grantTokens := None
    ));

    expect versionKeyResult.Failure?;
    expect versionKeyResult.error == Types.KeyStoreException(
      message := "Found more than one active key under: " + keyId + ". Resolve by calling ActiveKeyResolution API.");
  }
}
