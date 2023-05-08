// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsDynamoDB {
    import DDB = Com.Amazonaws.Dynamodb
    import opened StandardLibrary.UInt

    const tableNameTest : DDB.Types.TableName := "TestTable";
    const secIndex : DDB.Types.IndexName := "Active-Keys"

    // We should have basic tests for what the MPL is using DDB for.
    // MPL will interact with DDB through GET, PUT, and Query

    // Queries are used in the Hierarchy Keyring for OnEncrypt
    method {:test} BasicQueryTests() {
        var attributeNameMap := map[
          "#status"       := "Status",
          "#keyNamespace" := "keyNamespace"
        ];

        var attributeValueMap: DDB.Types.AttributeMap := map[
          ":status" := DDB.Types.AttributeValue.S("ACTIVE"),
          ":keyNamespace" := DDB.Types.AttributeValue.S("aws-kms-h")
        ];


        var queryInput := DDB.Types.QueryInput(
            TableName := tableNameTest,
            IndexName := DDB.Wrappers.Some(secIndex),
            Select := DDB.Wrappers.None,
            AttributesToGet := DDB.Wrappers.None,
            Limit := DDB.Wrappers.None,
            ConsistentRead :=  DDB.Wrappers.None,
            KeyConditions := DDB.Wrappers.None,
            QueryFilter := DDB.Wrappers.None,
            ConditionalOperator := DDB.Wrappers.None,
            ScanIndexForward := DDB.Wrappers.None,
            ExclusiveStartKey := DDB.Wrappers.None,
            ReturnConsumedCapacity :=  DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            FilterExpression := DDB.Wrappers.None,
            KeyConditionExpression := DDB.Wrappers.Some(
                "#status = :status and #keyNamespace = :keyNamespace"
            ),
            ExpressionAttributeNames := DDB.Wrappers.Some(attributeNameMap),
            ExpressionAttributeValues := DDB.Wrappers.Some(attributeValueMap)
        );
       // TODO actually call BasicQueryTest; need to stand up infra first
    }
 
    // MPL uses Get in the Hierarchy Keyring for OnDecrypt
    method {:test} BasicGetTests() {
        var Key2Get: DDB.Types.Key := map[
          "keyNamespace" := DDB.Types.AttributeValue.S("aws-kms-h"),
          "Version" := DDB.Types.AttributeValue.N("1")
        ];
        var getInput := DDB.Types.GetItemInput(
            TableName := tableNameTest,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
       );
       // TODO actually call BasicGetTest; need to stand up infra first
    }

    method BasicQueryTest(
        nameonly input: DDB.Types.QueryInput
    ) 
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.Query(input);

        expect(ret.Success?);

        var queryOutput := ret.value;

        expect queryOutput.Items.Some?;

        var queryItem := queryOutput.Items.value;
        expect |queryItem| > 0;

        var item := queryItem[0];

        // we only expect these keys
        expect item.Keys == {"keyNamespace", "Version", "amzn-ddbec-enc", "amzn-ddbec-metadata", "Status"};
        // we expect that for every key there is a value
        expect |item.Keys| == |item.Values|; 

    }

    method BasicGetTest(
        nameonly input: DDB.Types.GetItemInput
    )
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.GetItem(input);

        expect(ret.Success?);

        var itemOutput := ret.value;
        expect itemOutput.Item.Some?;

        var item := itemOutput.Item.value;
        expect item.Keys == {"keyNamespace", "Version", "amzn-ddbec-enc", "amzn-ddbec-metadata", "Status"};
        expect |item.Keys| == |item.Values|;
    }
}
