// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"

include "GetKeys.dfy"
include "CreateKeyStoreTable.dfy"
include "CreateKeys.dfy"

module AwsCryptographyKeyStoreOperations refines AbstractAwsCryptographyKeyStoreOperations {
  import opened AwsArnParsing
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  import MaterialProviders
  import GetKeys
  import CreateKeys
  import CreateKeyStoreTable

  datatype Config = Config(
    nameonly ddbTableName: DDB.TableName,
    nameonly kmsClient: ComAmazonawsKmsTypes.IKMSClient,
    nameonly ddbClient: ComAmazonawsDynamodbTypes.IDynamoDBClient
  )

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
  {
    && DDB.IsValid_TableName(config.ddbTableName)
    && config.kmsClient.ValidState()
    && config.ddbClient.ValidState()
  }

  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {
    config.kmsClient.Modifies + config.ddbClient.Modifies
  }

  predicate CreateKeyStoreEnsuresPublicly(input: CreateKeyStoreInput, output: Result<CreateKeyStoreOutput, Error>)
  {true}

  method CreateKeyStore ( config: InternalConfig, input: CreateKeyStoreInput )
    returns (output: Result<CreateKeyStoreOutput, Error>)
    ensures output.Success? ==>
      && AwsArnParsing.ParseAmazonDynamodbTableName(output.value.tableArn).Success?
      && AwsArnParsing.ParseAmazonDynamodbTableName(output.value.tableArn).value == config.ddbTableName
  {
    :- Need(
      DDB.IsValid_IndexName("Active-Keys-" + config.ddbTableName),
      Types.KeyStoreException(message := "Invalid Table Name length.")
    );

    var ddbTableArn :- CreateKeyStoreTable.CreateKeyStoreTable(config.ddbTableName, config.ddbClient);
    :- Need(
      && AwsArnParsing.ParseAmazonDynamodbTableName(ddbTableArn).Success?
      && var tableName := AwsArnParsing.ParseAmazonDynamodbTableName(ddbTableArn);
      && tableName.value == config.ddbTableName,
      Types.KeyStoreException(message := "Configured DDB Table Name does not match parsed Table Name from DDB Table Arn.") 
    );

    output := Success(Types.CreateKeyStoreOutput(tableArn := ddbTableArn));
  }

  predicate CreateKeyEnsuresPublicly(input: CreateKeyInput, output: Result<CreateKeyOutput, Error>)
  {true}

  method CreateKey(config: InternalConfig, input: CreateKeyInput)
    returns (output: Result<CreateKeyOutput, Error>)
  {
    :- Need(
      DDB.IsValid_TableName(config.ddbTableName),
      Types.KeyStoreException(message := "Invalid Table Name length.")
    );

    output := CreateKeys.CreateBranchAndBeaconKeys(input, config.ddbTableName, config.kmsClient, config.ddbClient);
  }
  
  predicate VersionKeyEnsuresPublicly(input: VersionKeyInput, output: Result<(), Error>)
  {true}

  method VersionKey(config: InternalConfig, input: VersionKeyInput)
    returns (output: Result<(), Error>)
  {
    return Failure(KeyStoreException(message := "Implement me"));
  }

  predicate GetActiveBranchKeyEnsuresPublicly(input: GetActiveBranchKeyInput, output: Result<GetActiveBranchKeyOutput, Error>)
  {true}

  method GetActiveBranchKey(config: InternalConfig, input: GetActiveBranchKeyInput) 
    returns (output: Result<GetActiveBranchKeyOutput, Error>)
  {
    :- Need(
      DDB.IsValid_IndexName("Active-Keys-" + config.ddbTableName),
      Types.KeyStoreException(message := "Invalid table name length.")
    );
    output := GetKeys.GetActiveKeyAndUnwrap(input, config.ddbTableName, config.kmsClient, config.ddbClient);
  }

  predicate GetBranchKeyVersionEnsuresPublicly(input: GetBranchKeyVersionInput, output: Result<GetBranchKeyVersionOutput, Error>)
  {true}

  method GetBranchKeyVersion(config: InternalConfig, input: GetBranchKeyVersionInput)
    returns (output: Result<GetBranchKeyVersionOutput, Error>)
  {
    :- Need(
      |input.branchKeyVersion| == 16,
      Types.KeyStoreException(message := "Invalid branch key version length.")
    );
    output := GetKeys.GetBranchKeyVersion(input, config.ddbTableName, config.kmsClient, config.ddbClient);
  }

  predicate GetBeaconKeyEnsuresPublicly(input: GetBeaconKeyInput, output: Result<GetBeaconKeyOutput, Error>)
  {true}

  method GetBeaconKey(config: InternalConfig, input: GetBeaconKeyInput)
    returns (output: Result<GetBeaconKeyOutput, Error>)
  {
    output := GetKeys.GetBeaconKeyAndUnwrap(input, config.ddbTableName, config.kmsClient, config.ddbClient);
  }
}
