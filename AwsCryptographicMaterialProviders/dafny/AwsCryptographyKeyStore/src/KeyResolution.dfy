// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "CreateKeyStoreTable.dfy"
include "GetKeys.dfy"
include "CreateKeys.dfy"

//  We are able to add these files because the mpl and the keystore are the same code base
//  even though the mpl and the key store are different services
include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

module KeyResolution {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import opened CreateKeyStoreTable
  import opened GetKeys
  import opened CreateKeys
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  
  method ActiveBranchKeysResolution(
    input: Types.BranchKeyStatusResolutionInput,
    tableName: DDB.TableName,
    logicalKeyStoreName: string,
    kmsKeyArn: Types.KmsKeyArn,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (res: Result<(), Types.Error>)
    requires KMS.IsValid_KeyIdType(kmsKeyArn)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
  {
    var maybeActiveBranchKeys := GetKeys.QueryForActiveBranchKey(input.branchKeyIdentifier, tableName, ddbClient);
    var activeBranchKeys :- maybeActiveBranchKeys
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    
    :- Need(
      && activeBranchKeys.Items.Some?
      && |activeBranchKeys.Items.value| > 1,
      E("Only found 1 Active Branch Key under: " + input.branchKeyIdentifier + ". No need to call the BranchKeyStatusResolution API")
    );

    :- Need(
      forall resp <- activeBranchKeys.Items.value :: validActiveBranchKey?(resp),
      E("Malformed Branch Key entry")
    );
    
    var latestActiveBranchKey := SortByTime(activeBranchKeys.Items.value);
    var activeBranchKeysAsSet := ToSet(activeBranchKeys.Items.value);

    assert forall activeKey <- activeBranchKeysAsSet - {latestActiveBranchKey} :: validActiveBranchKey?(activeKey)
      by {
        assert forall resp <- activeBranchKeys.Items.value :: validActiveBranchKey?(resp);
        reveal ToSet();
      }

    var nonLatestActiveBranchKeys := activeBranchKeysAsSet - {latestActiveBranchKey};

    var reEncryptedDecryptOnlyBranchKeysDDMap :- ReEncryptedNonLatestActiveBranchKeys(
      nonLatestActiveBranchKeys,
      logicalKeyStoreName,
      kmsKeyArn,
      grantTokens,
      kmsClient
    );

    var writeResolvedActiveBranchKeys :- WriteDecryptOnlyBranchKeys(
      reEncryptedDecryptOnlyBranchKeysDDMap,
      tableName,
      ddbClient 
    );
    
    var maybeOneActiveKey := GetKeys.QueryForActiveBranchKey(input.branchKeyIdentifier, tableName, ddbClient); 
    var oneActiveBranchKey :- maybeOneActiveKey
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    
    :- Need(
      && oneActiveBranchKey.Items.Some?
      && |oneActiveBranchKey.Items.value| == 1,
      E("Failed to resolve multiple ACTIVE branch keys under branch-key-identifier: " + 
          input.branchKeyIdentifier + 
          ". Consider calling the BranchKeyStatusResolution API again."
        )
    );

    return Success(());
  }

  method ReEncryptedNonLatestActiveBranchKeys(activeKeys: set<branchKeyItem>, logicalKeyStoreName: string, kmsKeyArn: Types.KmsKeyArn, grantTokens: KMS.GrantTokenList, kmsClient: KMS.IKMSClient)
    returns (res: Result<seq<DDB.AttributeMap>, Types.Error>)
    requires KMS.IsValid_KeyIdType(kmsKeyArn) // Remove?
    requires forall activeKey : branchKeyItem | activeKey in activeKeys :: validActiveBranchKey?(activeKey)
    requires kmsClient.ValidState() 
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
  {
    var tmpActiveKeySet := activeKeys;
    var decryptOnlyBranchKeys: seq<DDB.AttributeMap> := [];

    while tmpActiveKeySet != {}
      decreases |tmpActiveKeySet|
    {
      var currentActiveKey: branchKeyItem :| currentActiveKey in tmpActiveKeySet;
      
      :- Need(
        currentActiveKey[KMS_FIELD].S == kmsKeyArn,
        Types.KeyStoreException(message := "Configured AWS KMS Key ARN does not match KMS Key ARN for branch-key-id: " + currentActiveKey[BRANCH_KEY_IDENTIFIER_FIELD].S)
      );

      var oldActiveBranchKeyEncryptionContext := activeBranchKeyEncryptionContext(
        currentActiveKey[BRANCH_KEY_IDENTIFIER_FIELD].S,
        currentActiveKey[TYPE_FIELD].S[|BRANCH_KEY_TYPE_PREFIX|..],
        currentActiveKey[KEY_CREATE_TIME].S,
        logicalKeyStoreName,
        currentActiveKey[KMS_FIELD].S
      );

      var decryptOnlyBranchKeyEncryptionContext := decryptOnlyBranchKeyEncryptionContext(
        currentActiveKey[BRANCH_KEY_IDENTIFIER_FIELD].S,
        currentActiveKey[TYPE_FIELD].S[|BRANCH_KEY_TYPE_PREFIX|..],
        currentActiveKey[KEY_CREATE_TIME].S,
        logicalKeyStoreName,
        currentActiveKey[KMS_FIELD].S
      );

      var decryptOnlyBranchKey :- ReEncryptBranchKeyDecryptOnly(
        currentActiveKey[BRANCH_KEY_FIELD].B,
        oldActiveBranchKeyEncryptionContext,
        decryptOnlyBranchKeyEncryptionContext,
        kmsKeyArn,
        grantTokens,
        kmsClient
      );

      var decryptOnlyBranchKeyDDBMap := ToBranchKeyItemAttributeMap(decryptOnlyBranchKeyEncryptionContext, decryptOnlyBranchKey.CiphertextBlob.value);
      decryptOnlyBranchKeys := decryptOnlyBranchKeys + [decryptOnlyBranchKeyDDBMap];

      tmpActiveKeySet := tmpActiveKeySet - {currentActiveKey};
    }
    res := Success(decryptOnlyBranchKeys);
  }

  method WriteDecryptOnlyBranchKeys(decryptOnlyBranchKeys: seq<DDB.AttributeMap>, tableName: DDB.TableName, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<(), Types.Error>)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
  {
    var transactWriteItemList := [];
    for i := 0 to |decryptOnlyBranchKeys|
    {  
      :- Need(
        validVersionBranchKey?(decryptOnlyBranchKeys[i]),
        Types.KeyStoreException(message := "Unable to write key material to Key Store: " + tableName)
      );

      var decryptOnlyBranchKeyTransactWriteItem := CreateTransactWritePutItem(decryptOnlyBranchKeys[i], tableName);
      transactWriteItemList := transactWriteItemList + [decryptOnlyBranchKeyTransactWriteItem];
      
      // TransactWrites Only allow up to 25 write item requests
      // if it is the case we have more than 25 we will segment the writes in
      // batches
      if |transactWriteItemList| == 25 ||
        ((1 <= |transactWriteItemList| <= 25) && (|transactWriteItemList| == |decryptOnlyBranchKeys|)) 
      {
        var transactRequest := DDB.TransactWriteItemsInput(
          TransactItems := transactWriteItemList,
          ReturnConsumedCapacity := None,
          ReturnItemCollectionMetrics := None,
          ClientRequestToken := None
        );
        var maybeTransactWriteResponse := ddbClient.TransactWriteItems(transactRequest);
        var transactWriteItemsResponse :- maybeTransactWriteResponse
          .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
        transactWriteItemList := [];
      }
    }
    res := Success(());
  }

}
