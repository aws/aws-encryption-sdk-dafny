// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "CreateKeyStoreTable.dfy"

include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

module GetKeys {
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import opened CreateKeyStoreTable
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import MPL = AwsCryptographyMaterialProvidersTypes

  const TYPE_FIELD := "type";
  const BRANCH_KEY_TYPE_PREFIX := "version:";
  const BRANCH_KEY_IDENTIFIER_FIELD := "branch-key-id";
  const TABLE_FIELD := "tablename";
  
  const BRANCH_KEY_FIELD := "enc";
  
  const KEY_CONDITION_EXPRESSION := "#branch_key_id = :branch_key_id and #status = :status";
  const EXPRESSION_ATTRIBUTE_NAMES := map[
    "#branch_key_id" := "branch-key-id",
    "#status"       := "status"
  ];
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := ":status";
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE := "ACTIVE";
  const EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := ":branch_key_id";
  const gsiPreFix := "Active-Keys-";
  
  type baseKeyStoreItem = m: DDB.AttributeMap | baseKeyStoreItemHasRequiredAttributes?(m) witness *
  predicate method baseKeyStoreItemHasRequiredAttributes?(m: DDB.AttributeMap) {
    && "branch-key-id" in m && m["branch-key-id"].S?
    && "type" in m && m["type"].S?
    && "status" in m && m["status"].S?
    && "create-time" in m && m["create-time"].S?
    && "hierarchy-version" in m && m["hierarchy-version"].N?
    && BRANCH_KEY_FIELD in m && m[BRANCH_KEY_FIELD].B?
    && KMS.IsValid_CiphertextType(m[BRANCH_KEY_FIELD].B)
    && var tmpM := m - {BRANCH_KEY_FIELD};
    && forall k | k in tmpM :: ValueToString(tmpM[k]).Success?
  }
  predicate method validBeaconKeyItem?(m: DDB.AttributeMap) {
    && baseKeyStoreItemHasRequiredAttributes?(m)
    && m["type"].S == "beacon:true"
    && m["status"].S == "SEARCH"
  }

  type branchKeyItem = m: DDB.AttributeMap | validActiveBranchKey?(m) witness *
  predicate method validActiveBranchKey?(m: DDB.AttributeMap) {
    && baseKeyStoreItemHasRequiredAttributes?(m)
    && m["status"].S == "ACTIVE"
    && |m["type"].S| > |BRANCH_KEY_TYPE_PREFIX|
  }

  type versionBranchKeyItem = m: DDB.AttributeMap | validVersionBranchKey?(m) witness *
  predicate method validVersionBranchKey?(m: DDB.AttributeMap) {
    && baseKeyStoreItemHasRequiredAttributes?(m)
    && (m["status"].S == "ACTIVE" || m["status"].S == "DECRYPT_ONLY")
    && |m["type"].S| > |BRANCH_KEY_TYPE_PREFIX|
  }
  
  function method ValueToString(a: DDB.AttributeValue): Result<string, Types.Error>
  {
    // TODO: come back and agree on how we would like to represent 
    // the other types. Look at DynamoToStruct.dfy to see how 
    // DBE is doing this conversion.
    // This is allowing us to bind the type of the value to the encryption context
    // we pass to KMS; we could also do a runtime check to check for this
    match a {
      case S(s) => Success(a.S)
      case N(n) => Success(a.N)
      // For now we only support AttributeValues that are either String or Number
      // AttributeValues, we have not specified how to represent attributes other than these
      // two, we SHOULD include them but we have to agree how to turn the underlying
      // type into a string/bytes so that they could be turned to UTF8 bytes to pass KMS.
      case _ => Failure(E("Type not supported"))
    }
  }

  method GetActiveKeyAndUnwrap(input: Types.GetActiveBranchKeyInput, tableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<Types.GetActiveBranchKeyOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    requires DDB.IsValid_IndexName(gsiPreFix + tableName) 
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var keyStoreGsi := gsiPreFix + tableName;
    
    var expressionAttributeValues : DDB.AttributeMap := map[
      EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := DDB.AttributeValue.S(input.branchKeyIdentifier),
      EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := DDB.AttributeValue.S(EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE)
    ];

    var queryInput := DDB.QueryInput(
      TableName := tableName,
      IndexName := Some(keyStoreGsi),
      Select := None,
      AttributesToGet := None,
      Limit := None,
      ConsistentRead :=  None,
      KeyConditions := None,
      QueryFilter := None,
      ConditionalOperator := None,
      ScanIndexForward := None,
      ExclusiveStartKey := None,
      ReturnConsumedCapacity :=  None,
      ProjectionExpression := None,
      FilterExpression := None,
      KeyConditionExpression := Some(KEY_CONDITION_EXPRESSION),
      ExpressionAttributeNames := Some(EXPRESSION_ATTRIBUTE_NAMES),
      ExpressionAttributeValues := Some(expressionAttributeValues)
    );
    var maybeQueryResponse := ddbClient.Query(queryInput);
    var queryResponse :- maybeQueryResponse
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    
    :- Need(
      && queryResponse.Items.Some?
      && |queryResponse.Items.value| > 0,
      E("No item found for corresponding branch key identifier.")
    );

    :- Need(
      forall resp <- queryResponse.Items.value :: validActiveBranchKey?(resp),
      E("Malformed Branch Key entry")
    );

    var branchKeyRecord := SortByTime(queryResponse.Items.value);
    
    :- Need(
      && input.awsKmsKeyArn.Some?
      && ValidateKmsKeyId(input.awsKmsKeyArn.value).Success?,
      E("Must supply AWS KMS Key ARN or AWS invalid KMS Key ARN")
    );

    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("GetActiveBranchKey received invalid grant tokens")
    );
    
    var branchKeyResponse :- decryptKeyStoreItem(branchKeyRecord, input.awsKmsKeyArn.value, grantTokens.value, tableName, kmsClient);
    var branchKeyVersion := branchKeyRecord["type"].S[|BRANCH_KEY_TYPE_PREFIX|..];
    var branchKeyVersionUtf8 :- UTF8.Encode(branchKeyVersion).MapFailure(e => E(e));

    return Success(Types.GetActiveBranchKeyOutput(
      branchKeyMaterials := MPL.BranchKeyMaterials(
        branchKey := branchKeyResponse.Plaintext.value,
        branchKeyVersion := branchKeyVersionUtf8
      )
    ));
  }

  method GetBranchKeyVersion(input: Types.GetBranchKeyVersionInput, tableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<Types.GetBranchKeyVersionOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    requires |input.branchKeyVersion| == 16
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var dynamoDbKey: DDB.Key := map[
      BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(input.branchKeyIdentifier),
      TYPE_FIELD := DDB.AttributeValue.S(BRANCH_KEY_TYPE_PREFIX + input.branchKeyVersion)
    ];
    var ItemRequest := DDB.GetItemInput(
      Key := dynamoDbKey,
      TableName := tableName,
      AttributesToGet := None,
      ConsistentRead :=  None,
      ReturnConsumedCapacity := None,
      ProjectionExpression := None,
      ExpressionAttributeNames := None 
    );

    var maybeGetItem := ddbClient.GetItem(ItemRequest);
    var getItemResponse :- maybeGetItem
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    
    :- Need(
      getItemResponse.Item.Some?,
      E("No item found for corresponding branch key identifier.")
    );

    :- Need(
      validVersionBranchKey?(getItemResponse.Item.value),
      E("Malformed Branch Key entry")
    );
    var branchKeyRecord: versionBranchKeyItem := getItemResponse.Item.value;

    :- Need(
      && input.awsKmsKeyArn.Some?
      && ValidateKmsKeyId(input.awsKmsKeyArn.value).Success?,
      E("Must supply AWS KMS Key ARN or AWS invalid KMS Key ARN")
    );

    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("GetBranchKeyVersion received invalid grant tokens")
    );

    var maybeBranchKeyResponse := decryptKeyStoreItem(branchKeyRecord, input.awsKmsKeyArn.value, grantTokens.value, tableName, kmsClient);
    var branchKeyResponse :- maybeBranchKeyResponse;

    var branchKeyVersion := branchKeyRecord["type"].S[|BRANCH_KEY_TYPE_PREFIX|..];
    var branchKeyVersionUtf8 :- UTF8.Encode(branchKeyVersion).MapFailure(e => E(e));

    return Success(Types.GetBranchKeyVersionOutput(
      branchKeyMaterials := MPL.BranchKeyMaterials(
        branchKey := branchKeyResponse.Plaintext.value,
        branchKeyVersion := branchKeyVersionUtf8
      )
    ));
  }
  
  //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
  //# This operation MUST be supplied a `branchKeyId`, `kmsKeyId`, and a 
  //# list of `Grant Tokens` as input.
  method GetBeaconKeyAndUnwrap(input: Types.GetBeaconKeyInput, tableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient) 
    returns (res: Result<Types.GetBeaconKeyOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
    //# MUST call AWS DDB `GetItem`
    //# using the `branch-key-id` as the Partition Key and "beacon:true" value as the Sort Key.
    var dynamoDbKey: DDB.Key := map[
      BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(input.branchKeyIdentifier),
      TYPE_FIELD := DDB.AttributeValue.S("beacon:true")
    ];
    
    var ItemRequest := DDB.GetItemInput(
      Key := dynamoDbKey,
      TableName := tableName,
      AttributesToGet := None,
      ConsistentRead :=  None,
      ReturnConsumedCapacity := None,
      ProjectionExpression := None,
      ExpressionAttributeNames := None 
    );

    var maybeGetItem := ddbClient.GetItem(ItemRequest);
    var getItemResponse :- maybeGetItem
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    
    :- Need(
      getItemResponse.Item.Some?,
      E("No item found for corresponding branch key identifier.")
    );

    :- Need(
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
      //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../branch-key-store.md#record-format).
      //# If the record does not contain the defined fields, OnEncrypt MUST fail.
      validBeaconKeyItem?(getItemResponse.Item.value),
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
      //# If the record does not contain the defined fields, this operation MUST fail.
      //# If the record does not contain "SEARCH" as the "status" field, this operation MUST fail.
      E("Malformed Branch Key entry")
    );
  
    var beaconKeyItem: baseKeyStoreItem := getItemResponse.Item.value;
    :- Need(
      && input.awsKmsKeyArn.Some?
      && ValidateKmsKeyId(input.awsKmsKeyArn.value).Success?,
      E("Must supply AWS KMS Key ARN or AWS invalid KMS Key ARN")
    );

    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("GetBeaconKey received invalid grant tokens")
    );
    
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
    //# The operation MUST decrypt the beacon key according to the [AWS KMS Branch Key Decryption](#aws-kms-branch-key-decryption) section.
    var beaconKeyResponse :- decryptKeyStoreItem(beaconKeyItem, input.awsKmsKeyArn.value, grantTokens.value, tableName, kmsClient);

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkeyi
    //# This operation MUST output the decrypted beacon key and branch key version.
    return Success(Types.GetBeaconKeyOutput(
      beaconKeyMaterials := MPL.BeaconKeyMaterials(
        beaconKeyIdentifier := input.branchKeyIdentifier,
        beaconKey := Some(beaconKeyResponse.Plaintext.value),
        hmacKeys := None
      )
    ));
  }
  
  method decryptKeyStoreItem(
    branchKeyRecord: baseKeyStoreItem,
    awsKmsKey: AwsKmsIdentifierString,
    grantTokens: KMS.GrantTokenList,
    tableName: DDB.TableName,
    kmsClient: KMS.IKMSClient
  )
    returns (output: Result<KMS.DecryptResponse, Types.Error>)
    requires baseKeyStoreItemHasRequiredAttributes?(branchKeyRecord)
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
    //= type=implication
    //# The operation MUST use the configured `KMS SDK Client` to decrypt the value of the branch key field.
    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
    ensures output.Success?
      ==> 
        && output.value.KeyId.Some?
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
        //= type=implication
        //# - The `KeyId` field in the AWS KMS response MUST equal the provided AWS KMS key identifier.
        && output.value.KeyId.value == awsKmsKey
        && output.value.Plaintext.Some?
        && 32 == |output.value.Plaintext.value|
  {
    var wrappedBranchKey: KMS.CiphertextType := branchKeyRecord[BRANCH_KEY_FIELD].B;

    var encCtxDdbMap := branchKeyRecord - {BRANCH_KEY_FIELD};

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
    //# The operation MUST create a branch key [encryption context](../structures.md#encryption-context).
    var encCtxMap: map<string, string> :=
      map k <- encCtxDdbMap ::
        k := ValueToString(encCtxDdbMap[k]).value;
    encCtxMap := encCtxMap + map[TABLE_FIELD := tableName];
    
    var decryptRequest :=
      KMS.DecryptRequest(
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
        //# - `KeyId` MUST be the provided kmsKeyId provided as input to the key store operation.
        KeyId := Some(awsKmsKey),
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
        //# - `CiphertextBlob` MUST be the `enc` AWS DDB response value.
        CiphertextBlob := wrappedBranchKey,
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
        //# - `EncryptionContext` MUST be the branch key encryption context map.
        EncryptionContext := Some(encCtxMap),
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-decryption
        //# - `GrantTokens` MUST be the [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token) 
        GrantTokens := Some(grantTokens),
        EncryptionAlgorithm := None
      );

    var maybeDecryptResponse := kmsClient.Decrypt(decryptRequest);
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#getbeaconkey
    //# If the beacon key fails to decrypt, this operation MUST fail.
    var decryptResponse :- maybeDecryptResponse
      .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

    :- Need(
      && decryptResponse.KeyId.Some?
      && decryptResponse.KeyId.value == awsKmsKey
      && decryptResponse.Plaintext.Some?
      && 32 == |decryptResponse.Plaintext.value|,
      E("Invalid response from KMS Decrypt")
    );
    return Success(decryptResponse);
  }
  
  method SortByTime(queryResponse: DDB.ItemList)
    returns (output: branchKeyItem)
    requires |queryResponse| > 0
    requires 
      && (forall resp <- queryResponse :: 
        && validActiveBranchKey?(resp))
    ensures validActiveBranchKey?(output)
  { 
    if |queryResponse| == 1 {
      return queryResponse[0];
    }

    var newestBranchKey: branchKeyItem := queryResponse[0];
    
    for i := 1 to |queryResponse| {
      var tmp: branchKeyItem := queryResponse[i];
      var a := newestBranchKey["create-time"].S;
      var b := tmp["create-time"].S;

      if !LexicographicLessOrEqual(a, b, CharGreater) {
        newestBranchKey := queryResponse[i];
      } else {
        var versionA := newestBranchKey["type"].S[|BRANCH_KEY_TYPE_PREFIX|..];
        var versionB := tmp["type"].S[|BRANCH_KEY_TYPE_PREFIX|..];
        if !LexicographicLessOrEqual(versionA, versionB, CharGreater) {
          newestBranchKey := queryResponse[i];
        }
      }
    }

    return newestBranchKey;
  }

  function method CharGreater(a: char, b: char): bool 
  {
    a > b
  } 
}
