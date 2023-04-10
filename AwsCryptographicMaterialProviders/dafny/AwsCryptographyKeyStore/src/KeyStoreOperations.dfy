// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"

include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

module KeyStoreOperations {
  import opened StandardLibrary
  import opened Wrappers
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import MPL = AwsCryptographyMaterialProvidersTypes

  const VERSION_FIELD := "version";
  const BRANCH_KEY_IDENTIFIER_FIELD := "branch-key-id";
  
  const BRANCH_KEY_FIELD := "enc";
  
  type branchKeyItem = m: DDB.AttributeMap | branchKeyItemHasRequiredAttributes?(m) witness *
  predicate method branchKeyItemHasRequiredAttributes?(m: DDB.AttributeMap) {
    && "branch-key-id" in m && m["branch-key-id"].S?
    && "version" in m && m["version"].S?
    && "status" in m && m["status"].S?
    && "create-time" in m && m["create-time"].S?
    && "hierarchy-version" in m && m["hierarchy-version"].N?
    && "type" in m && m["type"].S?
    && "table-name" in m && m["table-name"].S?
    && BRANCH_KEY_FIELD in m && m[BRANCH_KEY_FIELD].B?
    && KMS.IsValid_CiphertextType(m[BRANCH_KEY_FIELD].B)
    && var tmpM := m - {BRANCH_KEY_FIELD};
    && forall k | k in tmpM :: ValueToString(tmpM[k]).Success?
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
  
  method GetBeaconKeyAndUnwrap(input: Types.GetBeaconKeyInput, tableName: DDB.TableName, kmsClient: KMS.IKMSClient, ddbClient: DDB.IDynamoDBClient) 
    returns (res: Result<Types.GetBeaconKeyOutput, Types.Error>)
    requires kmsClient.ValidState() && ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()
    ensures res.Success? ==> |res.value.beaconKey| == 32
  {
    var dynamoDbKey: DDB.Key := map[
      BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(input.branchKeyIdentifier),
      VERSION_FIELD := DDB.AttributeValue.S("beacon-key")
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

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
    //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../branch-key-store.md#record-format).
    //# If the record does not contain the defined fields, OnEncrypt MUST fail.
    :- Need(
      branchKeyItemHasRequiredAttributes?(getItemResponse.Item.value),
      E("Malformed Branch Key entry")
    );
  
    var branchKeyRecord: branchKeyItem := getItemResponse.Item.value;
    :- Need(
      && input.awsKmsKeyArn.Some?
      && ValidateKmsKeyId(input.awsKmsKeyArn.value).Success?,
      E("Must supply AWS KMS Key ARN or AWS invalid KMS Key ARN")
    );
    // var _ :- ValidateKmsKeyId(input.awsKmsKeyArn.value);

    // Vvar parsedAwsKmsId: AwsKmsIdentifierString := ParseAwsKmsIdentifier(input.awsKmsKeyArn.value).value as string;
    
    var maybeBeaconKeyResponse := decryptBeaconKey(branchKeyRecord, input.awsKmsKeyArn.value, kmsClient);
    var beaconKeyResponse :- maybeBeaconKeyResponse;

    return Success(Types.GetBeaconKeyOutput(beaconKey := beaconKeyResponse.Plaintext.value));
  }
  
  method decryptBeaconKey(
    branchKeyRecord: branchKeyItem,
    awsKmsKey: AwsKmsIdentifierString,
    kmsClient: KMS.IKMSClient
  )
    returns (output: Result<KMS.DecryptResponse, Types.Error>)

    requires branchKeyItemHasRequiredAttributes?(branchKeyRecord)
    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
    ensures output.Success?
      ==> 
        && output.value.KeyId.Some?
        && output.value.KeyId.value == awsKmsKey
        && output.value.Plaintext.Some?
        && 32 == |output.value.Plaintext.value|
  {
    var wrappedBranchKey: KMS.CiphertextType := branchKeyRecord[BRANCH_KEY_FIELD].B;

    var encCtxDdbMap := branchKeyRecord - {BRANCH_KEY_FIELD};

    var encCtxMap: map<string, string> :=
      map k <- encCtxDdbMap ::
        k := ValueToString(encCtxDdbMap[k]).value; 
    
    var decryptRequest :=
      KMS.DecryptRequest(
        KeyId := Some(awsKmsKey),
        CiphertextBlob := wrappedBranchKey,
        EncryptionContext := Some(encCtxMap),
        GrantTokens := None,
        EncryptionAlgorithm := None
      );

    var maybeDecryptResponse := kmsClient.Decrypt(decryptRequest);
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

  function method E(s : string) : Types.Error {
    Types.KeyStoreException(message := s)
  }
}
