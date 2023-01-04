// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "AwsKmsArnParsing.dfy"
include "AwsKmsUtils.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsHierarchicalKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AwsKmsUtils
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import opened AlgorithmSuites
  import Keyring
  import Materials
  import Time
  import Random
  import Digest
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import UTF8
  import HKDF
  import HMAC
  import opened AESEncryption
  
  // UTF-8 encoded "TRUSS_KEYWRAP_ENC"
  const TRUSS_KEYWRAP_ENC: UTF8.ValidUTF8Bytes :=
    var s := [0x54, 0x52, 0x55, 0x53, 0x53, 0x5f, 0x4b, 0x45, 0x59, 0x57, 0x52, 0x41, 0x50, 0x5f, 0x45, 0x4e, 0x43];
    assert UTF8.ValidUTF8Range(s, 0, 17);
    s
  
  // UTF-8 encoded "TRUSS_KEYWRAP_MAC"
  const TRUSS_KEYWRAP_MAC: UTF8.ValidUTF8Bytes :=
    var s := [0x54, 0x52, 0x55, 0x53, 0x53, 0x5f, 0x4b, 0x45, 0x59, 0x57, 0x52, 0x41, 0x50, 0x5f, 0x4d, 0x41, 0x43];
    assert UTF8.ValidUTF8Range(s, 0, 17);
    s

  // UTF-8 encoded "ACTIVE"
  const ACTIVE: UTF8.ValidUTF8Bytes :=
    var s := [0x41,  0x43,  0x54,  0x49,  0x56,  0x45];
    assert UTF8.ValidUTF8Range(s, 0, 6);
    s

  
  type branchKeyRecordMap = m: map<DDB.AttributeName, DDB.AttributeValue> | branchKeyRecordMap?(m) witness *
  predicate branchKeyRecordMap?(m: map<DDB.AttributeName, DDB.AttributeValue>) {
    "amzn-ddbec-metadata" in m && "amzn-ddbec-enc" in m && "keyNamespace" in m 
      && "Version" in m && "Status" in m
  }
  
  type branchKeyRecordEncContextMap = m: map<DDB.AttributeName, DDB.AttributeValue> | branchKeyRecordEncContextMap?(m) witness *
  predicate branchKeyRecordEncContextMap?(m: map<DDB.AttributeName, DDB.AttributeValue>) {
    "Partition Key" in m && "Region" in m && "Sort Key" in m && "TableName" in m
  }


  class AwsKmsHierarchicalKeyring
    extends Keyring.VerifiableInterface
  {
    const kmsClient: KMS.IKeyManagementServiceClient
    const ddbClient: DDB.IDynamoDB_20120810Client
    const branchKeyId: string
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const branchKeysTableName: string
    const ttlMilliseconds: int64
    const maxCacheSize: int32
    const grantTokens: KMS.GrantTokenList

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && kmsClient.ValidState()
      && ddbClient.ValidState()
      && kmsClient.Modifies <= Modifies
      && ddbClient.Modifies <= Modifies
      && History !in kmsClient.Modifies
      && History !in ddbClient.Modifies
    }

    constructor (
      // MUST provide and MUST NOT be null.
      kmsClient: KMS.IKeyManagementServiceClient,
      // MUST provide
      awsKmsKey: string,
      // MAY provide a list of grant tokens
      grantTokens: KMS.GrantTokenList,

      // MUST provide and MUST NOT be null
      ddbClient: DDB.IDynamoDB_20120810Client,
      // MUST provide
      branchKeysTableName: string,
      // MUST provide
      branchKeyId: string,
      // MAY provide
      ttlMilliseconds: int64,

      maxCacheSize: int32
    )
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires DDB.IsValid_TableName(branchKeysTableName)
      requires kmsClient.ValidState() && ddbClient.ValidState()
      requires maxCacheSize >= 1
      ensures
        && this.kmsClient           == kmsClient
        && this.awsKmsKey           == awsKmsKey
        && this.grantTokens         == grantTokens
        && this.ddbClient           == ddbClient
        && this.branchKeysTableName == branchKeysTableName
        && this.branchKeyId         == branchKeyId
        && this.ttlMilliseconds     == ttlMilliseconds
        && this.maxCacheSize        == maxCacheSize
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - kmsClient.Modifies - ddbClient.Modifies)
    {
      var parsedAwsKmsId    := ParseAwsKmsIdentifier(awsKmsKey);

      this.kmsClient           := kmsClient;
      this.awsKmsKey           := awsKmsKey;
      this.awsKmsArn           := parsedAwsKmsId.value;
      this.grantTokens         := grantTokens;
      this.ddbClient           := ddbClient;
      this.branchKeysTableName := branchKeysTableName;
      this.branchKeyId         := branchKeyId;
      this.ttlMilliseconds     := ttlMilliseconds;
      this.maxCacheSize        := maxCacheSize;
      
      History := new Types.IKeyringCallHistory();
      Modifies := {History} + kmsClient.Modifies + ddbClient.Modifies;
    }


    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}
    
    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History) 
      ensures res.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          res.value.materials
        )
      ensures StringifyEncryptionContext(input.materials.encryptionContext).Failure?
      ==>
        res.Failure?

      ensures !KMS.IsValid_KeyIdType(awsKmsKey)
      ==>
        res.Failure?
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(message := "Add Hierarchical Crypto Operation Logic"));
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}
    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials)
    {
      return Failure(Types.AwsCryptographicMaterialProvidersException(message := "Add Hierarchical Crypto Operation Logic"));
    }
  }
}
