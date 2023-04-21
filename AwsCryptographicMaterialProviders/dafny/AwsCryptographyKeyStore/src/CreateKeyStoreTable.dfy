// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"

module CreateKeyStoreTable {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes

  // KeyStore Definitions 
  const attrDef: DDB.AttributeDefinitions := [
    DDB.AttributeDefinition(
      AttributeName := "branch-key-id",
      AttributeType := DDB.ScalarAttributeType.S),
    DDB.AttributeDefinition(
      AttributeName := "status",
      AttributeType := DDB.ScalarAttributeType.S),
    DDB.AttributeDefinition(
      AttributeName := "type",
      AttributeType := DDB.ScalarAttributeType.S)
  ];
  const keySchema: DDB.KeySchema := [
    DDB.KeySchemaElement(
      AttributeName := "branch-key-id",
      KeyType := DDB.KeyType.HASH),
    DDB.KeySchemaElement(
      AttributeName := "type",
      KeyType := DDB.KeyType.RANGE)
  ];

  // GSI 
  const keySchemaGsi: DDB.KeySchema := [
    DDB.KeySchemaElement(
      AttributeName := "branch-key-id",
      KeyType := DDB.KeyType.HASH),
    DDB.KeySchemaElement(
      AttributeName := "status",
      KeyType := DDB.KeyType.RANGE)
  ];
  const gsiProjection: DDB.Projection := DDB.Projection(
    ProjectionType := Some(DDB.ProjectionType.ALL),
    NonKeyAttributes := None
  ); 
  const GSI_NAME := "Active-Keys";

  // type tableName = tn : DDB.TableName;
  type keyStoreDescription = t: DDB.TableDescription | keyStoreHasExpectedConstruction?(t) witness *
  predicate method keyStoreHasExpectedConstruction?(t: DDB.TableDescription) {
    && t.AttributeDefinitions.Some? && t.KeySchema.Some? && t.GlobalSecondaryIndexes.Some? && t.TableName.Some? && t.TableArn.Some?
    && ToSet(t.AttributeDefinitions.value) == ToSet(attrDef)
    && ToSet(t.KeySchema.value) == ToSet(keySchema)
    && |t.GlobalSecondaryIndexes.value| >= 1
    && var gsiList := t.GlobalSecondaryIndexes.value;
    && exists gsi | gsi in gsiList :: 
      && gsi.IndexName.Some? && gsi.KeySchema.Some? && gsi.Projection.Some?
      && gsi.IndexName.value == GSI_NAME
      && ToSet(gsi.KeySchema.value) == ToSet(keySchemaGsi)
      && gsi.Projection.value == gsiProjection
  }

  method CreateKeyStoreTable(tableName: DDB.TableName, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<string, Types.Error>)
    requires ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    requires DDB.IsValid_IndexName(GSI_NAME) 
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
  {
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
    //# This operation MUST first calls the DDB::DescribeTable API with the configured `tableName`.
    var maybeDescribeTableResponse := ddbClient.DescribeTable(
      DDB.DescribeTableInput(
        TableName := tableName
      )
    );

    if maybeDescribeTableResponse.Failure? {
      var error := maybeDescribeTableResponse.error;
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
      //# If the client responds with a `ResourceNotFoundException`,
      //# then this operation MUST continue and
      if error.ResourceNotFoundException? {
        var gsi: DDB.GlobalSecondaryIndexList := [
          DDB.GlobalSecondaryIndex(
            IndexName := GSI_NAME,
            KeySchema := keySchemaGsi,
            Projection := gsiProjection,
            ProvisionedThroughput := None
          )
        ];

        //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
        //# MUST call [AWS DDB CreateTable](https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_CreateTable.html)
        //# with the following specifics:
        var maybeCreateTableResponse := ddbClient.CreateTable(
          DDB.CreateTableInput(
            AttributeDefinitions := attrDef,
            TableName := tableName,
            //= aws-encryption-sdk-specification/framework/branch-key-store.md#keyschema
            //# The following KeySchema MUST be configured on the table:
            KeySchema := keySchema,
            LocalSecondaryIndexes := None,
            //= aws-encryption-sdk-specification/framework/branch-key-store.md#globalsecondary-indexes
            //# The table MUST configure a single GlobalSecondaryIndex:
            GlobalSecondaryIndexes := Some(gsi),
            BillingMode := Some(DDB.BillingMode.PAY_PER_REQUEST) ,
            ProvisionedThroughput :=  None,
            StreamSpecification := None,
            SSESpecification := None,
            Tags := None,
            TableClass := None
          )
        );

        if maybeCreateTableResponse.Failure? {
          expect maybeCreateTableResponse.error.LimitExceededException? || maybeCreateTableResponse.error.ResourceInUseException?;
          expect maybeCreateTableResponse.error.message.Some?;
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //# If the operation fails to create table, the operation MUST fail.
          res := Failure(E(maybeCreateTableResponse.error.message.value));
        } else {
          expect maybeCreateTableResponse.value.TableDescription.Some?;
          expect keyStoreHasExpectedConstruction?(maybeCreateTableResponse.value.TableDescription.value);
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //# If the operation successfully creates a table, the operation MUST return the AWS DDB Table Arn
          //# back to the caller.
          res := Success(maybeCreateTableResponse.value.TableDescription.value.TableArn.value);
        }
      } else {
        expect error.InternalServerError?;
        expect error.message.Some?;
        res := Failure(E(error.message.value));
      }
    } else {
      expect maybeDescribeTableResponse.value.Table.Some?;
      var tableDescription := maybeDescribeTableResponse.value.Table.value;
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
      //# If the response is successful, this operation validates that the table has the expected
      //# [KeySchema](#keyschema) and [GlobalSecondaryIndexes](#globalsecondary-indexes) as defined below.
      //# If these values do not match, this operation MUST yield an error.
      :- Need(
        && keyStoreHasExpectedConstruction?(tableDescription),
        E("Configured table name does not conform to expected Key Store construction.")
      );
      res := Success(tableDescription.TableArn.value);
    }
  } 
  
  function method E(s : string) : Types.Error {
    Types.KeyStoreException(message := s)
  }
}
