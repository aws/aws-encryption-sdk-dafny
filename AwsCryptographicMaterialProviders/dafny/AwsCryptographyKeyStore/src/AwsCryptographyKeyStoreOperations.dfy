// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

include "GetKeys.dfy"
include "CreateKeyStoreTable.dfy"
include "CreateKeys.dfy"
include "KeyResolution.dfy"

module AwsCryptographyKeyStoreOperations refines AbstractAwsCryptographyKeyStoreOperations {
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  import CreateKeys
  import CreateKeyStoreTable
  import KeyResolution
  import GetKeys

  datatype Config = Config(
    nameonly id: string,
    nameonly ddbTableName: DDB.TableName,
    nameonly logicalKeyStoreName: string,
    nameonly kmsConfiguration: KMSConfiguration,
    nameonly grantTokens: KMS.GrantTokenList,
    nameonly kmsClient: ComAmazonawsKmsTypes.IKMSClient,
    nameonly ddbClient: ComAmazonawsDynamodbTypes.IDynamoDBClient
  )

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
  {
    && DDB.IsValid_TableName(config.ddbTableName)
    && DDB.IsValid_IndexName(CreateKeyStoreTable.GSI_NAME)
    && KMS.IsValid_KeyIdType(config.kmsConfiguration.kmsKeyArn)
    && config.kmsClient.ValidState()
    && config.ddbClient.ValidState()
  }

  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {
    config.kmsClient.Modifies + config.ddbClient.Modifies
  }
  predicate GetKeyStoreInfoEnsuresPublicly(output: Result<GetKeyStoreInfoOutput, Error>)
  {true}

  method GetKeyStoreInfo(config: InternalConfig)
    returns (output: Result<GetKeyStoreInfoOutput, Error>)
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#getkeystoreinfo
    //= type=implication
    //# This operation MUST return the key store information in this key store configuration.
    ensures output.Success? ==>
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#getkeystoreinfo
      //= type=implication
      //# This MUST include:
      && output.value.keyStoreId == config.id 
      && output.value.keyStoreName == config.ddbTableName
      && output.value.logicalKeyStoreName == config.logicalKeyStoreName
      && output.value.grantTokens == config.grantTokens
      && output.value.kmsConfiguration == config.kmsConfiguration
  {
    output := Success(
      Types.GetKeyStoreInfoOutput(
        keyStoreId := config.id,
        keyStoreName := config.ddbTableName,
        logicalKeyStoreName := config.logicalKeyStoreName,
        grantTokens := config.grantTokens,
        kmsConfiguration := config.kmsConfiguration
      )
    );
  }

  predicate CreateKeyStoreEnsuresPublicly(input: CreateKeyStoreInput, output: Result<CreateKeyStoreOutput, Error>)
  {true}

  method CreateKeyStore ( config: InternalConfig, input: CreateKeyStoreInput )
    returns (output: Result<CreateKeyStoreOutput, Error>)
    ensures output.Success? ==>
      && AwsArnParsing.ParseAmazonDynamodbTableName(output.value.tableArn).Success?
      && AwsArnParsing.ParseAmazonDynamodbTableName(output.value.tableArn).value == config.ddbTableName
  {
    var ddbTableArn :- CreateKeyStoreTable.CreateKeyStoreTable(config.ddbTableName, config.ddbClient);
    :- Need(
      && AwsArnParsing.ParseAmazonDynamodbTableName(ddbTableArn).Success?
      && var tableName := AwsArnParsing.ParseAmazonDynamodbTableName(ddbTableArn);
      && tableName.value == config.ddbTableName,
      Types.KeyStoreException(message := "Configured DDB Table Name does not match parsed Table Name from DDB Table Arn.") 
    );

    output := Success(Types.CreateKeyStoreOutput(tableArn := ddbTableArn));
  }

  predicate CreateKeyEnsuresPublicly(output: Result<CreateKeyOutput, Error>)
  {true}

  method CreateKey(config: InternalConfig)
    returns (output: Result<CreateKeyOutput, Error>)
  {
    output := CreateKeys.CreateBranchAndBeaconKeys(config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }
  
  predicate VersionKeyEnsuresPublicly(input: VersionKeyInput, output: Result<(), Error>)
  {true}

  method VersionKey(config: InternalConfig, input: VersionKeyInput)
    returns (output: Result<(), Error>)
  {
    output := CreateKeys.VersionActiveBranchKey(input, config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }

  predicate GetActiveBranchKeyEnsuresPublicly(input: GetActiveBranchKeyInput, output: Result<GetActiveBranchKeyOutput, Error>)
  {true}

  method GetActiveBranchKey(config: InternalConfig, input: GetActiveBranchKeyInput) 
    returns (output: Result<GetActiveBranchKeyOutput, Error>)
  {
    output := GetKeys.GetActiveKeyAndUnwrap(input, config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }

  predicate GetBranchKeyVersionEnsuresPublicly(input: GetBranchKeyVersionInput, output: Result<GetBranchKeyVersionOutput, Error>)
  {true}

  method GetBranchKeyVersion(config: InternalConfig, input: GetBranchKeyVersionInput)
    returns (output: Result<GetBranchKeyVersionOutput, Error>)
  {
    output := GetKeys.GetBranchKeyVersion(input, config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }

  predicate GetBeaconKeyEnsuresPublicly(input: GetBeaconKeyInput, output: Result<GetBeaconKeyOutput, Error>)
  {true}

  method GetBeaconKey(config: InternalConfig, input: GetBeaconKeyInput)
    returns (output: Result<GetBeaconKeyOutput, Error>)
  {
    output := GetKeys.GetBeaconKeyAndUnwrap(input, config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }

  predicate BranchKeyStatusResolutionEnsuresPublicly(input: BranchKeyStatusResolutionInput, output: Result<(), Error>)
  {true}

  method BranchKeyStatusResolution(config: InternalConfig, input: BranchKeyStatusResolutionInput)
    returns (output: Result<(), Error>)
  {
    output := KeyResolution.ActiveBranchKeysResolution(input, config.ddbTableName, config.logicalKeyStoreName, config.kmsConfiguration.kmsKeyArn, config.grantTokens, config.kmsClient, config.ddbClient);
  }
}
