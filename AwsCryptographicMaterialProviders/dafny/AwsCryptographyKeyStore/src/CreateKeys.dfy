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

  // A GenerateDataKeyWithoutPlaintext of request size 32 returns a ciphertext size of 184 bytes.
  const KMS_GEN_KEY_NO_PLAINTEXT_LENGTH_32 := 184;

  type branchKeyItem = m: map<string, string> | branchKeyContextHasRequiredFields?(m) witness *
  predicate method branchKeyContextHasRequiredFields?(m: map<string, string>) {
    && KEY_IDENTIFIER_FIELD in m
    && TYPE_FIELD in m
    && KEY_STATUS in m
    && KEY_CREATE_TIME in m
    && HIERARCHY_VERSION in m
    && TABLE_FIELD in m
  }

  function method activeBranchKeyEncryptionContext(id: string, version: string, timestamp: string, tableName: string): (output: map<string, string>)
    ensures branchKeyContextHasRequiredFields?(output)
  {
    map[
      KEY_IDENTIFIER_FIELD := id,
      TYPE_FIELD := BRANCH_KEY_TYPE_PREFIX + version,
      KEY_STATUS := "ACTIVE",
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := tableName,
      HIERARCHY_VERSION := "1"
    ]
  }

  function method beaconKeyEncryptionContext(id: string, timestamp: string, tableName: string): (output: map<string, string>)
    ensures branchKeyContextHasRequiredFields?(output)
  {
    map[
      KEY_IDENTIFIER_FIELD := id,
      TYPE_FIELD := BEACON_KEY_TYPE_VALUE,
      KEY_STATUS := "SEARCH",
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := tableName,
      HIERARCHY_VERSION := "1"
    ]
  }

  method CreateBranchAndBeaconKeys(input: Types.CreateKeyInput, ddbTableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<Types.CreateKeyOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(ddbTableName)
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var branchKeyId :- UUID.GenerateUUID()
      .MapFailure(e => E(e));
    var timestamp :- Time.GetCurrentTimeStamp()
      .MapFailure(e => E(e));

    :- Need(
      && ValidateKmsKeyId(input.awsKmsKeyArn).Success?,
      E("Must supply AWS KMS Key ARN or AWS invalid KMS Key ARN")
    );

    var grantTokens := GetValidGrantTokens(input.grantTokens);
    :- Need(
      && grantTokens.Success?,
      E("CreateKey received invalid grant tokens")
    );
    
    // Branch Key Creation
    var branchKeyVersion :- UUID.GenerateUUID()
      .MapFailure(e => E(e));
    
    var activeBranchKeyEncryptionContext: branchKeyItem := activeBranchKeyEncryptionContext(branchKeyId, branchKeyVersion, timestamp, ddbTableName);

    var branchKeyWithoutPlaintext :- GenerateKey(
      activeBranchKeyEncryptionContext,
      input.awsKmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    // Beacon Key Creation
    var beaconKeyEncryptionContext: branchKeyItem := beaconKeyEncryptionContext(branchKeyId, timestamp, ddbTableName);

    var beaconKeyWithoutPlaintext :- GenerateKey(
      beaconKeyEncryptionContext,
      input.awsKmsKeyArn,
      grantTokens.value,
      kmsClient
    );

    var transactWriteItemsToKeyStore :- WriteNewKeyToStore(
      activeBranchKeyEncryptionContext,
      branchKeyWithoutPlaintext.CiphertextBlob.value,
      beaconKeyEncryptionContext,
      beaconKeyWithoutPlaintext.CiphertextBlob.value, 
      ddbTableName,
      ddbClient
    );

    res := Success(Types.CreateKeyOutput(
      branchKeyIdentifier := branchKeyId 
    ));
  }


  method GenerateKey(
    encryptionContext: map<string, string>,
    awsKmsKey: AwsKmsIdentifierString,
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
    branchKeyItem: branchKeyItem,
    wrappedBranchKey: seq<uint8>,
    beaconKeyItem: branchKeyItem,
    wrappedBeaconKey: seq<uint8>,
    tableName: DDB.TableName,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (res: Result<DDB.TransactWriteItemsOutput, Types.Error>)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
  {
    var branchKeyDDBMap := ToBranchKeyItemAttributeMap(branchKeyItem, wrappedBranchKey);
    var branchKeyTransactWriteItem := CreateTransactWritePutItem(branchKeyDDBMap, tableName);

    var beaconKeyDDBMap := ToBranchKeyItemAttributeMap(beaconKeyItem, wrappedBeaconKey);
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

  function method ToBranchKeyItemAttributeMap(m: branchKeyItem, k: seq<uint8>): (output: DDB.AttributeMap)
  {
    map[
      KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(m[KEY_IDENTIFIER_FIELD]),
      TYPE_FIELD := DDB.AttributeValue.S(m[TYPE_FIELD]),
      KEY_STATUS := DDB.AttributeValue.S(m[KEY_STATUS]),
      KEY_FIELD := DDB.AttributeValue.B(k),
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

  method VersionActiveBranchKey(input: Types.VersionKeyInput, ddbTableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<(), Types.Error>)
  {
    res := Failure(E("Implement"));
  }
}
