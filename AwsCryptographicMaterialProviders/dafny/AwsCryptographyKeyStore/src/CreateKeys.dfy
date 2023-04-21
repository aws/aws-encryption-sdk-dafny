// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "CreateKeyStoreTable.dfy"
include "GetKeys.dfy"

include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

module CreateKeys {
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import opened CreateKeyStoreTable
  import opened GetKeys
  import opened Seq
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import UUID
  import Time

  const KEY_IDENTIFIER_FIELD := "branch-key-id";
  const TYPE_FIELD := "type";
  const BRANCH_KEY_TYPE_PREFIX := "version:";
  const BEACON_KEY_TYPE_VALUE := "beacon:true";
  const KEY_FIELD := "enc";
  const KEY_STATUS := "status";
  const KEY_CREATE_TIME := "create-time";
  const HIERARCHY_VERSION := "hierarchy-version";
  const TABLE_FIELD := "tablename";
  const KMS_FIELD := "kms-arn";

  // A GenerateDataKeyWithoutPlaintext of request size 32 returns a ciphertext size of 184 bytes.
  const KMS_GEN_KEY_NO_PLAINTEXT_LENGTH_32 := 184;

  type BranchKeyContext = m: map<string, string> | branchKeyContextHasRequiredFields?(m) witness *
  predicate method branchKeyContextHasRequiredFields?(m: map<string, string>) {
    && KEY_IDENTIFIER_FIELD in m
    && TYPE_FIELD in m
    && KEY_STATUS in m
    && KEY_CREATE_TIME in m
    && HIERARCHY_VERSION in m
    && TABLE_FIELD in m
    && KMS_FIELD in m
  }

  function method activeBranchKeyEncryptionContext(id: string, version: string, timestamp: string, tableName: string, kmsKeyArn: string): (output: map<string, string>)
    ensures branchKeyContextHasRequiredFields?(output)
  {
    map[
      KEY_IDENTIFIER_FIELD := id,
      TYPE_FIELD := BRANCH_KEY_TYPE_PREFIX + version,
      KEY_STATUS := "ACTIVE",
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := tableName,
      KMS_FIELD := kmsKeyArn,
      HIERARCHY_VERSION := "1"
    ]
  }

  function method decryptOnlyBranchKeyEncryptionContext(id: string, version: string, timestamp: string, tableName: string, kmsKeyArn: string): (output: map<string, string>)
    ensures branchKeyContextHasRequiredFields?(output)
  {
    map[
      KEY_IDENTIFIER_FIELD := id,
      TYPE_FIELD := BRANCH_KEY_TYPE_PREFIX + version,
      KEY_STATUS := "DECRYPT_ONLY",
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := tableName,
      KMS_FIELD := kmsKeyArn,
      HIERARCHY_VERSION := "1"
    ]
  }

  function method beaconKeyEncryptionContext(id: string, timestamp: string, tableName: string, kmsKeyArn: string): (output: map<string, string>)
    ensures branchKeyContextHasRequiredFields?(output)
  {
    map[
      KEY_IDENTIFIER_FIELD := id,
      TYPE_FIELD := BEACON_KEY_TYPE_VALUE,
      KEY_STATUS := "SEARCH",
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := tableName,
      KMS_FIELD := kmsKeyArn,
      HIERARCHY_VERSION := "1"
    ]
  }

  method CreateBranchAndBeaconKeys(input: Types.CreateKeyInput, ddbTableName: DDB.TableName, kmsKeyArn: Types.KmsKeyArn, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<Types.CreateKeyOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(ddbTableName)
    requires KMS.IsValid_KeyIdType(kmsKeyArn)
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var maybeBranchKeyId := UUID.GenerateUUID();
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //# - `branchKeyId`: a new guid. This guid MUST be [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt)
    var branchKeyId :- maybeBranchKeyId
      .MapFailure(e => Types.KeyStoreException(message := e));
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //# - `timestamp`: a timestamp for the current time. 
    //# This MUST be in ISO8601 format in UTC, to microsecond precision (e.g. “YYYY-MM-DDTHH:mm:ss.ssssssZ“)
    var timestamp :- Time.GetCurrentTimeStamp()
      .MapFailure(e => E(e));

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //# - MAY provide a list of Grant Tokens
    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("CreateKey received invalid grant tokens")
    );
    
    var maybeBranchKeyVersion := UUID.GenerateUUID();
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //# - `version`: a new guid. This guid MUST be [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt)
    var branchKeyVersion :- maybeBranchKeyVersion
      .MapFailure(e => Types.KeyStoreException(message := e));

    :- Need(
      && maybeBranchKeyId.Success?
      && maybeBranchKeyVersion.Success?,
      Types.KeyStoreException(message := "Failed to generate UUID for Key ID or Key Version.")
    );
    
    var activeBranchKeyEncryptionContext: BranchKeyContext := activeBranchKeyEncryptionContext(branchKeyId, branchKeyVersion, timestamp, ddbTableName, kmsKeyArn);

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //# The operation MUST call [AWS KMS API GenerateDataKeyWithoutPlaintext]
    //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKeyWithoutPlaintext.html).
    var branchKeyWithoutPlaintext :- GenerateKey(
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
      //# - `EncryptionContext` MUST be the [encryption context for branch keys](#encryption-context).
      activeBranchKeyEncryptionContext,
      kmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    // Beacon Key Creation
    var beaconKeyEncryptionContext: BranchKeyContext := beaconKeyEncryptionContext(branchKeyId, timestamp, ddbTableName, kmsKeyArn);

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //# The operation MUST call [AWS KMS API GenerateDataKeyWithoutPlaintext]
    //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKeyWithoutPlaintext.html).
    var beaconKeyWithoutPlaintext :- GenerateKey(
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
      //# - `EncryptionContext` MUST be the [encryption context for beacon keys](#encryption-context).
      beaconKeyEncryptionContext,
      kmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //# If creation of both keys is successful, 
    //# this operation MUST call [Amazon DynamoDB API TransactWriteItems]
    //# (https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_TransactWriteItems.html).
    var transactWriteItemsToKeyStore :- WriteNewKeyToStore(
      activeBranchKeyEncryptionContext,
      branchKeyWithoutPlaintext.CiphertextBlob.value,
      beaconKeyEncryptionContext,
      beaconKeyWithoutPlaintext.CiphertextBlob.value,
      ddbTableName,
      ddbClient
    );

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //# If writing to the key store succeeds, the operation MUST return the branch-key-id that maps to both
    //# the branch key and the beacon key.
    res := Success(Types.CreateKeyOutput(
      branchKeyIdentifier := branchKeyId 
    ));
  }


  method GenerateKey(
    encryptionContext: map<string, string>,
    awsKmsKey: KMS.KeyIdType,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient
  ) 
    returns (res: Result<KMS.GenerateDataKeyWithoutPlaintextResponse, Types.Error>)
    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
    ensures res.Success? ==>
      && res.value.KeyId.Some?
      && res.value.CiphertextBlob.Some?
      && |res.value.CiphertextBlob.value| == KMS_GEN_KEY_NO_PLAINTEXT_LENGTH_32
      && |kmsClient.History.GenerateDataKeyWithoutPlaintext| > 0
      && KMS.IsValid_CiphertextType(res.value.CiphertextBlob.value)
      && var kmsOperation := Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).input;
      && var kmsOperationOutput := Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output;
      && kmsOperationOutput.Success?
      && KMS.GenerateDataKeyWithoutPlaintextRequest(
          KeyId := awsKmsKey,
          EncryptionContext := Some(encryptionContext),
          KeySpec := None,
          NumberOfBytes := Some(32),
          GrantTokens := Some(grantTokens)
        ) == kmsOperation
      && kmsOperationOutput.value.CiphertextBlob.Some?
      && kmsOperationOutput.value.CiphertextBlob == res.value.CiphertextBlob
      && kmsOperationOutput.value.KeyId.Some?
      && kmsOperationOutput.value.KeyId == res.value.KeyId
  {
    var generatorRequest := KMS.GenerateDataKeyWithoutPlaintextRequest(
      KeyId := awsKmsKey,
      EncryptionContext := Some(encryptionContext),
      KeySpec := None,
      NumberOfBytes := Some(32),
      GrantTokens := Some(grantTokens)
    );

    var maybeGenerateResponse := kmsClient.GenerateDataKeyWithoutPlaintext(generatorRequest);
    var generateResponse :- maybeGenerateResponse
      .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));
    
    :- Need(
      && generateResponse.KeyId.Some?
      && ParseAwsKmsIdentifier(generateResponse.KeyId.value).Success?,
      Types.KeyStoreException(
        message := "Invalid response from KMS GenerateDataKey:: Invalid Key Id")
    );

    :- Need(
      && generateResponse.CiphertextBlob.Some?
      && |generateResponse.CiphertextBlob.value| == KMS_GEN_KEY_NO_PLAINTEXT_LENGTH_32
      && KMS.IsValid_CiphertextType(generateResponse.CiphertextBlob.value),
      Types.KeyStoreException(
        message := "Invalid response from AWS KMS GeneratedDataKey: Invalid ciphertext")
    );
    
    return Success(generateResponse);
  }

  method WriteNewKeyToStore(
    branchKeyContext: BranchKeyContext,
    wrappedBranchKey: seq<uint8>,
    beaconKeyContext: BranchKeyContext,
    wrappedBeaconKey: seq<uint8>,
    tableName: DDB.TableName,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (res: Result<DDB.TransactWriteItemsOutput, Types.Error>)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
  {
    var branchKeyDDBMap := ToBranchKeyItemAttributeMap(branchKeyContext, wrappedBranchKey);
    var branchKeyTransactWriteItem := CreateTransactWritePutItem(branchKeyDDBMap, tableName);

    var beaconKeyDDBMap := ToBranchKeyItemAttributeMap(beaconKeyContext, wrappedBeaconKey);
    var beaconKeyTransactWriteItem := CreateTransactWritePutItem(beaconKeyDDBMap, tableName);
    
    :- Need(
      // In order to be certain we are writing something that is well formed
      // and something we will be able to get or query we need to ensure it has certain properties
      && validBeaconKeyItem?(beaconKeyDDBMap)
      && validActiveBranchKey?(branchKeyDDBMap),
      Types.KeyStoreException(message := "Unable to write key material to Key Store: " + tableName)
    );

    var items: DDB.TransactWriteItemList := [
      branchKeyTransactWriteItem,
      beaconKeyTransactWriteItem 
    ];

    var transactRequest := DDB.TransactWriteItemsInput(
      TransactItems := items,
      ReturnConsumedCapacity := None,
      ReturnItemCollectionMetrics := None,
      ClientRequestToken := None
    );

    var maybeTransactWriteResponse := ddbClient.TransactWriteItems(transactRequest);
    var transactWriteItemsResponse :- maybeTransactWriteResponse
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));

    res := Success(transactWriteItemsResponse);
  }

  method WriteVersionedKeyToStore(
    decryptOnlyBranchKey: DDB.AttributeMap,
    newActiveBranchKey: DDB.AttributeMap,
    tableName: DDB.TableName,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (res: Result<DDB.TransactWriteItemsOutput, Types.Error>)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
  {
    var decryptOnlyBranchKeyTransactWriteItem := CreateTransactWritePutItem(decryptOnlyBranchKey, tableName);
    var newActiveBranchKeyTransactWriteItem := CreateTransactWritePutItem(newActiveBranchKey, tableName);

    :- Need(
      // In order to be certain we are writing something that is well formed
      // and something we will be able to get or query we need to ensure it has certain properties
      && validActiveBranchKey?(newActiveBranchKey)
      && validVersionBranchKey?(decryptOnlyBranchKey),
      Types.KeyStoreException(message := "Unable to write key material to Key Store: " + tableName)
    );

    var items: DDB.TransactWriteItemList := [
      decryptOnlyBranchKeyTransactWriteItem,
      newActiveBranchKeyTransactWriteItem 
    ];
    
    var transactRequest := DDB.TransactWriteItemsInput(
      TransactItems := items,
      ReturnConsumedCapacity := None,
      ReturnItemCollectionMetrics := None,
      ClientRequestToken := None
    );
    
    var maybeTransactWriteResponse := ddbClient.TransactWriteItems(transactRequest);
    var transactWriteItemsResponse :- maybeTransactWriteResponse
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));

    res := Success(transactWriteItemsResponse);
  }

  // We specify that every item on the encryption context to KMS is stored in the branch/beacon key item.
  // This method allows us to convert from a BranchKeyContext map to a DDB.AttributeMap easily.
  function method ToBranchKeyItemAttributeMap(m: BranchKeyContext, k: seq<uint8>): (output: DDB.AttributeMap)
  {
    map[
      KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(m[KEY_IDENTIFIER_FIELD]),
      TYPE_FIELD := DDB.AttributeValue.S(m[TYPE_FIELD]),
      KEY_STATUS := DDB.AttributeValue.S(m[KEY_STATUS]),
      KEY_FIELD := DDB.AttributeValue.B(k),
      KMS_FIELD := DDB.AttributeValue.S(m[KMS_FIELD]),
      KEY_CREATE_TIME := DDB.AttributeValue.S(m[KEY_CREATE_TIME]),
      HIERARCHY_VERSION := DDB.AttributeValue.N(m[HIERARCHY_VERSION])
    ]
  }

  function method CreateTransactWritePutItem(item: DDB.AttributeMap, tableName: DDB.TableName): (output: DDB.TransactWriteItem)
  {
    DDB.TransactWriteItem(
      ConditionCheck := None,
      Put := Some(DDB.Put( 
        Item := item,
        TableName := tableName,
        ConditionExpression := None,
        ExpressionAttributeNames := None,
        ExpressionAttributeValues := None,
        ReturnValuesOnConditionCheckFailure := None)),
      Delete := None,
      Update := None
    )
  }

  method VersionActiveBranchKey(input: Types.VersionKeyInput, ddbTableName: DDB.TableName, kmsKeyArn: Types.KmsKeyArn, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<(), Types.Error>)
    requires KMS.IsValid_KeyIdType(kmsKeyArn)
    requires ddbClient.ValidState() && kmsClient.ValidState()
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var queryOutput :- QueryForActiveBranchKey(input.branchKeyIdentifier, ddbTableName, ddbClient);

    :- Need(
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../#record-format).
      //# If the record does not contain the defined fields, this operation MUST fail.
      && validActiveBranchKey?(queryOutput.Items.value[0])
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# If the `type` on the item is not prefixed by "version", this operation MUST fail.
      && queryOutput.Items.value[0][TYPE_FIELD].S[..|BRANCH_KEY_TYPE_PREFIX|] == BRANCH_KEY_TYPE_PREFIX,
      Types.KeyStoreException(message := "Active key for " + input.branchKeyIdentifier + " does not have required fields.")
    );
    
    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("CreateKey received invalid grant tokens")
    );

    var item := queryOutput.Items.value[0];
    
    :- Need(
      item[KMS_FIELD].S == kmsKeyArn,
      Types.KeyStoreException(message := "Configured AWS KMS Key ARN does not match KMS Key ARN for branch-key-id: " + item[BRANCH_KEY_IDENTIFIER_FIELD].S)
    );
    

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
    //= type=implication
    //# The operation MUST create a branch key [encryption context](./structures.md#encryption-context)
    //# from the branch AWS DDB query response according to [branch key encryption context](#encryption-context).
    var oldActiveBranchKeyEncryptionContext := activeBranchKeyEncryptionContext(
      item[KEY_IDENTIFIER_FIELD].S,
      item[TYPE_FIELD].S[|BRANCH_KEY_TYPE_PREFIX|..],
      item[KEY_CREATE_TIME].S,
      ddbTableName,
      item[KMS_FIELD].S
    );
    
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
    //= type=implication
    //# The operation MUST create a branch key [encryption context](./structures.md#encryption-context)
    //# for DECRYPT_ONLY branch keys according to the [decrypt only branch key encryption context](#decrypt_only-encryption-context).
    var decryptOnlyBranchKeyEncryptionContext: BranchKeyContext := decryptOnlyBranchKeyEncryptionContext(
      item[KEY_IDENTIFIER_FIELD].S,
      item[TYPE_FIELD].S[|BRANCH_KEY_TYPE_PREFIX|..],
      item[KEY_CREATE_TIME].S,
      ddbTableName,
      item[KMS_FIELD].S
    );

    var decryptOnlyBranchKey :- ReEncryptBranchKeyDecryptOnly(
      item[KEY_FIELD].B,
      oldActiveBranchKeyEncryptionContext,
      decryptOnlyBranchKeyEncryptionContext,
      kmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
    //# To create a new `ACTIVE` branch key under the supplied `branch-key-id` the operation
    //# MUST generate the following values:


    var maybeBranchKeyVersion := UUID.GenerateUUID();
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
    //# - `version`: a new guid. This guid MUST be [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt)
    var branchKeyVersion :- maybeBranchKeyVersion
      .MapFailure(e => Types.KeyStoreException(message := e));
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
    //# - `timestamp`: a timestamp for the current time. 
    //# This MUST be in ISO8601 format in UTC, to microsecond precision (e.g. “YYYY-MM-DDTHH:mm:ss.ssssssZ“)
    var timestamp :- Time.GetCurrentTimeStamp()
      .MapFailure(e => E(e));
    
    var newActiveBranchKeyEncryptionContext: BranchKeyContext := activeBranchKeyEncryptionContext(
      item[KEY_IDENTIFIER_FIELD].S,
      branchKeyVersion,
      timestamp,
      ddbTableName,
      kmsKeyArn 
    );

    var newBranchKeyWithoutPlaintext :- GenerateKey(
      newActiveBranchKeyEncryptionContext,
      kmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    var decryptOnlyBranchKeyDDBMap := ToBranchKeyItemAttributeMap(decryptOnlyBranchKeyEncryptionContext, decryptOnlyBranchKey.CiphertextBlob.value);
    var newActiveBranchKeyDDBMap := ToBranchKeyItemAttributeMap(newActiveBranchKeyEncryptionContext, newBranchKeyWithoutPlaintext.CiphertextBlob.value); 

    var writeRotatedMaterials :- WriteVersionedKeyToStore(
      decryptOnlyBranchKeyDDBMap,
      newActiveBranchKeyDDBMap,
      ddbTableName,
      ddbClient 
    );

    res := Success(());
  }

  method QueryForActiveBranchKey(branchKeyId: string, ddbTableName: DDB.TableName, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<DDB.QueryOutput, Types.Error>)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
    ensures 
      && |ddbClient.History.Query| > 0
      && var ddbOperationInput := Last(ddbClient.History.Query).input;
      && var ddbOperationOutput := Last(ddbClient.History.Query).output;
      && ddbOperationOutput.Success?
      && ddbOperationOutput.value.Items.Some?
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# There MUST only be one `ACTIVE` key. If there is more than one `ACTIVE` key, the operation MUST fail.
      && |ddbOperationOutput.value.Items.value| > 1
      ==> res.Failure?
    ensures 
      && |ddbClient.History.Query| > 0
      && var ddbOperationOutput := Last(ddbClient.History.Query).output;
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# 1. If the client is unable to fetch an `ACTIVE` key, GetActiveBranchKey MUST fail.
      && ddbOperationOutput.Failure?
      ==> res.Failure?
    ensures res.Success? ==>
      && |ddbClient.History.Query| > 0
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# This operation MUST make a DDB::Query to get the branch key at `branchKeyId` with status `ACTIVE`
      && var ddbOperationInput := Last(ddbClient.History.Query).input;
      && var ddbOperationOutput := Last(ddbClient.History.Query).output;
      && var expressionAttributeValues: DDB.AttributeMap := map[
        EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := DDB.AttributeValue.S(branchKeyId),
        EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := DDB.AttributeValue.S(STATUS_ACTIVE)];
      && ddbOperationOutput.Success?
      && ddbOperationInput.TableName == ddbTableName
      && ddbOperationInput.IndexName.Some?
      && ddbOperationInput.IndexName.value == CreateKeyStoreTable.GSI_NAME
      && ddbOperationInput.KeyConditionExpression.Some?
      && ddbOperationInput.KeyConditionExpression.value == STATUS_BRANCH_KEY_ID_MATCH_EXPRESSION
      && ddbOperationInput.ExpressionAttributeNames.Some?
      && ddbOperationInput.ExpressionAttributeNames.value == EXPRESSION_ATTRIBUTE_NAMES
      && ddbOperationInput.ExpressionAttributeValues.Some?
      && ddbOperationInput.ExpressionAttributeValues.value == expressionAttributeValues
      && ddbOperationOutput.value == res.value
    ensures res.Success?
      ==>
        && res.value.Items.Some?
        && |res.value.Items.value| == 1
  {
    var expressionAttributeValues : DDB.AttributeMap := map[
      EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := DDB.AttributeValue.S(branchKeyId),
      EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := DDB.AttributeValue.S(STATUS_ACTIVE)
    ];
    
    var queryInput := DDB.QueryInput(
      TableName := ddbTableName,
      IndexName := Some(CreateKeyStoreTable.GSI_NAME),
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
      KeyConditionExpression := Some(STATUS_BRANCH_KEY_ID_MATCH_EXPRESSION),
      ExpressionAttributeNames := Some(EXPRESSION_ATTRIBUTE_NAMES),
      ExpressionAttributeValues := Some(expressionAttributeValues)
    );
    
    var maybeQueryResponse := ddbClient.Query(queryInput);
    var queryResponse :- maybeQueryResponse
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));

    :- Need(
      && queryResponse.Items.Some?
      && |queryResponse.Items.value| == 1,
      E("Found more than one active key under: " + branchKeyId + ". Resolve by calling ActiveKeyResolution API.")
    );

    return Success(queryResponse);
  }

  method ReEncryptBranchKeyDecryptOnly(
    ciphertext: seq<uint8>,
    oldEncryptionContext: map<string, string>,
    decryptOnlyEncryptionContext: map<string, string>,
    awsKmsKey: KMS.KeyIdType,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient
  )
    returns (res: Result<KMS.ReEncryptResponse, Types.Error>)
    requires kmsClient.ValidState()
    requires KMS.IsValid_CiphertextType(ciphertext)
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
    ensures res.Success? ==>
      && res.value.CiphertextBlob.Some?
      && res.value.SourceKeyId.Some?
      && res.value.KeyId.Some?
      && res.value.SourceKeyId.value == awsKmsKey
      && res.value.KeyId.value == awsKmsKey
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
      //= type=implication
      //# The operation MUST use the configured `KMS SDK Client` to decrypt the value of the branch key field.
      && |kmsClient.History.ReEncrypt| > 0
      && KMS.IsValid_CiphertextType(res.value.CiphertextBlob.value)
      && var kmsOperationInput := Last(kmsClient.History.ReEncrypt).input;
      && var kmsOperationOutput := Last(kmsClient.History.ReEncrypt).output;
      && kmsOperationOutput.Success?
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
      //= type=implication
      //# When calling [AWS KMS API ReEncrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_ReEncrypt.html), 
      //# the key store operation MUST call with a request constructed as follows:
      && KMS.ReEncryptRequest(
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `CiphertextBlob` MUST be the encrypted branch key value that is stored in AWS DDB.
        CiphertextBlob := ciphertext,
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `SourceEncryptionContext` MUST be the branch key encryption context.
        SourceEncryptionContext := Some(oldEncryptionContext),
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `SourceKeyId` MUST be the AWS KMS Key ARN configured in the key store operation.
        SourceKeyId := Some(awsKmsKey),
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `DestinationKeyId` MUST be the AWS KMS Key ARN configured in the key store operation.
        DestinationKeyId := awsKmsKey,
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `DestinationEncryptionContext` MUST be the DECRYPT_ONLY branch key encryption context created.
        DestinationEncryptionContext := Some(decryptOnlyEncryptionContext),
        SourceEncryptionAlgorithm := None,
        DestinationEncryptionAlgorithm := None,
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#aws-kms-branch-key-reencryption
        //= type=implication
        //# - `GrantTokens` MUST be the [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token)
        GrantTokens := Some(grantTokens)
      ) == kmsOperationInput
      && kmsOperationOutput.value.CiphertextBlob.Some?
      && kmsOperationOutput.value.SourceKeyId.Some?
      && kmsOperationOutput.value.KeyId.Some?
      && kmsOperationOutput.value.CiphertextBlob.value == res.value.CiphertextBlob.value
      && kmsOperationOutput.value.SourceKeyId.value == res.value.SourceKeyId.value
      && kmsOperationOutput.value.KeyId.value == res.value.KeyId.value
  {
    var reEncryptRequest := KMS.ReEncryptRequest(
      CiphertextBlob := ciphertext,
      SourceEncryptionContext := Some(oldEncryptionContext),
      SourceKeyId := Some(awsKmsKey),
      DestinationKeyId := awsKmsKey,
      DestinationEncryptionContext := Some(decryptOnlyEncryptionContext),
      SourceEncryptionAlgorithm := None,
      DestinationEncryptionAlgorithm := None,
      GrantTokens := Some(grantTokens)
    );

    var maybeReEncryptResponse := kmsClient.ReEncrypt(reEncryptRequest);
    var reEncryptResponse :- maybeReEncryptResponse
      .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));
    
    :- Need(
      && reEncryptResponse.SourceKeyId.Some?
      && reEncryptResponse.KeyId.Some?
      && reEncryptResponse.SourceKeyId.value == awsKmsKey
      && reEncryptResponse.KeyId.value == awsKmsKey 
      && ParseAwsKmsIdentifier(reEncryptResponse.SourceKeyId.value).Success?
      && ParseAwsKmsIdentifier(reEncryptResponse.KeyId.value).Success?,
      Types.KeyStoreException(
        message := "Invalid response from KMS GenerateDataKey:: Invalid Key Id")
    );

    :- Need(
      && reEncryptResponse.CiphertextBlob.Some?
      && KMS.IsValid_CiphertextType(reEncryptResponse.CiphertextBlob.value),
      Types.KeyStoreException(
        message := "Invalid response from AWS KMS GeneratedDataKey: Invalid ciphertext")
    );

    return Success(reEncryptResponse);
  }
}
