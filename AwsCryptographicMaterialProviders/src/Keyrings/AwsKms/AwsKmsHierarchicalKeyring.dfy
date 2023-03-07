// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsUtils.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsHierarchicalKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsArnParsing
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
  import Aws.Cryptography.Primitives
  
  const BRANCH_KEY_STORE_GSI := "Active-Keys";
  const BRANCH_KEY_FIELD := "enc";
  const VERSION_FIELD := "version";
  const BRANCH_KEY_IDENTIFIER_FIELD := "branch-key-id";
  
  const KEY_CONDITION_EXPRESSION := "#status = :status and #branch_key_id = :branch_key_id";
  const EXPRESSION_ATTRIBUTE_NAMES := map[
    "#status"       := "status",
    "#branch_key_id" := "branch-key-id"
  ];
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := ":status";
  const EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE := "ACTIVE";
  const EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := ":branch_key_id";
  
  const H_WRAP_SALT_LEN: Types.PositiveInteger := 16;
  const H_WRAP_NONCE_LEN: Types.PositiveInteger := 12;
  const DERIVED_BRANCH_KEY_EXPECTED_LENGTH: Types.PositiveInteger := 32;
  const AES_256_ENC_KEY_LENGTH: int32 := 32;
  const AES_256_ENC_TAG_LENGTH: int32 := 16;
  const AES_256_ENC_IV_LENGTH: int32 := 12;
  const AES_256_ENC_ALG := Crypto.AES_GCM(
    keyLength := AES_256_ENC_KEY_LENGTH,
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
    //= type=implication
    //# MUST use an authentication tag byte of length 16.
    tagLength := AES_256_ENC_TAG_LENGTH,
    ivLength := AES_256_ENC_IV_LENGTH
  );

  const EXPECTED_EDK_CIPHERTEXT_LENGTH := 112;
  const EDK_CIPHERTEXT_VERSION_LENGTH: int32 := 36;
  const EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX := H_WRAP_SALT_LEN + H_WRAP_NONCE_LEN; 
  const EDK_CIPHERTEXT_VERSION_INDEX := EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX + EDK_CIPHERTEXT_VERSION_LENGTH;
  const EDK_CIPHERTEXT_KEY_INDEX := EDK_CIPHERTEXT_VERSION_INDEX + AES_256_ENC_KEY_LENGTH;

  
  type branchKeyItem = m: DDB.AttributeMap | branchKeyItemHasRequiredAttributes?(m) witness *
  predicate method branchKeyItemHasRequiredAttributes?(m: DDB.AttributeMap) {
    && "branch-key-id" in m && m["branch-key-id"].S?
    && "version" in m && m["version"].S?
    && "status" in m && m["status"].S?
    && "create-time" in m && m["create-time"].S?
    && "hierarchy-version" in m && m["hierarchy-version"].N?
    && BRANCH_KEY_FIELD in m && m[BRANCH_KEY_FIELD].B?
    && KMS.IsValid_CiphertextType(m[BRANCH_KEY_FIELD].B)
    && var tmpM := m - {BRANCH_KEY_FIELD};
    && forall k | k in tmpM :: ValueToString(tmpM[k]).Success?
  }

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#interface
  //= type=implication
  //# MUST implement the [AWS Encryption SDK Keyring interface](../keyring-interface.md#interface)
  class AwsKmsHierarchicalKeyring
    extends Keyring.VerifiableInterface
  {
    const kmsClient: KMS.IKeyManagementServiceClient
    const ddbClient: DDB.IDynamoDB_20120810Client
    const branchKeyId: string
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const branchKeyStoreArn: string
    const branchKeyStoreName: string
    const ttlSeconds: int64
    const maxCacheSize: Types.PositiveInteger
    const grantTokens: KMS.GrantTokenList
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const branchKeyStoreIndex: string

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && kmsClient.ValidState()
      && ddbClient.ValidState()
      && cryptoPrimitives.ValidState()
      && kmsClient.Modifies <= Modifies
      && ddbClient.Modifies <= Modifies
      && cryptoPrimitives.Modifies <= Modifies
      && History !in kmsClient.Modifies
      && History !in ddbClient.Modifies
      && History !in cryptoPrimitives.Modifies
      // TODO this should eventually be Valid branch key store arn
      && DDB.IsValid_TableName(this.branchKeyStoreName)
      && DDB.IsValid_IndexName(this.branchKeyStoreIndex)
    }

    constructor (
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS KMS SDK client
      kmsClient: KMS.IKeyManagementServiceClient,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS KMS key identifier
      awsKmsKey: string,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MAY provide a list of Grant Tokens
      grantTokens: KMS.GrantTokenList,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS DDB SDK client
      ddbClient: DDB.IDynamoDB_20120810Client,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS DDB Table ARN
      branchKeyStoreArn: string,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide a Branch Key Identifier
      branchKeyId: string,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MUST provide a cache limit TTL
      ttlSeconds: int64,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# - MAY provide a max cache size
      maxCacheSize: Types.PositiveInteger,
      cryptoPrimitives : Primitives.AtomicPrimitivesClient
    )
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#initialization
      //= type=implication
      //# The AWS KMS
      //# key identifier MUST be [a valid identifier](aws-kms-key-arn.md#a-
      //# valid-aws-kms-identifier).
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires ParseAmazonDynamodbTableName(branchKeyStoreArn).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires maxCacheSize >= 1
      requires DDB.IsValid_TableName(ParseAmazonDynamodbTableName(branchKeyStoreArn).value)
      requires kmsClient.ValidState() && ddbClient.ValidState() && cryptoPrimitives.ValidState()
      ensures
        && this.kmsClient    == kmsClient
        && this.awsKmsKey    == awsKmsKey
        && this.grantTokens  == grantTokens
        && this.ddbClient    == ddbClient
        && this.branchKeyStoreArn  == branchKeyStoreArn
        && this.branchKeyId  == branchKeyId
        && this.ttlSeconds   == ttlSeconds
        && this.maxCacheSize == maxCacheSize
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - kmsClient.Modifies - ddbClient.Modifies - cryptoPrimitives.Modifies)
    {
      var parsedAwsKmsId    := ParseAwsKmsIdentifier(awsKmsKey);
      var parsedBranchKeyStoreName := ParseAmazonDynamodbTableName(branchKeyStoreArn);
      
      this.kmsClient           := kmsClient;
      this.awsKmsKey           := awsKmsKey;
      this.awsKmsArn           := parsedAwsKmsId.value;
      this.grantTokens         := grantTokens;
      this.ddbClient           := ddbClient;
      this.branchKeyStoreArn   := branchKeyStoreArn;
      this.branchKeyStoreName  := parsedBranchKeyStoreName.value;
      this.branchKeyId         := branchKeyId;
      this.ttlSeconds          := ttlSeconds;
      this.maxCacheSize        := maxCacheSize;
      this.cryptoPrimitives    := cryptoPrimitives;
      this.branchKeyStoreIndex := BRANCH_KEY_STORE_GSI;
      
      History := new Types.IKeyringCallHistory();
      Modifies := {History} + kmsClient.Modifies + ddbClient.Modifies + cryptoPrimitives.Modifies;
    }


    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}
    
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials]
    //# (../structures.md#encryption-materials) as input.
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

      ensures !KMS.IsValid_KeyIdType(awsKmsKey)
      ==>
        res.Failure?
    {
      var materials := input.materials;
      var suite := materials.algorithmSuite;
      var aad :- EncryptionContextToAADHierarchy(materials.encryptionContext);

      var plaintextDataKey := materials.plaintextDataKey.UnwrapOr([]);

      if plaintextDataKey == [] {
        var randomKeyResult := cryptoPrimitives
          .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(suite)));
        var k' :- randomKeyResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
        plaintextDataKey := k';
      }
      
      var branchKeyIdUtf8 :- UTF8.Encode(this.branchKeyId)
        .MapFailure(WrapStringToError);
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
      //= type=implication
      //# The hierarchical keyring MUST attempt to obtain the hierarchical materials by querying 
      //# the backing branch keystore
      var hierarchicalMaterials :- GetActiveHierarchicalMaterials(branchKeyId, branchKeyIdUtf8);
      
      var branchKey := hierarchicalMaterials.branchKey;
      // TODO: determine the uuid byte encoding instead of the utf8 encoding
      var branchKeyVersion := hierarchicalMaterials.branchKeyVersion;
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
      //# The hierarchical keyring MUST:
      // (blank line for duvet)
      //# 1. Generate a 16 byte random salt using a secure source of randomness
      //# 1. Generate a 12 byte random iv using a secure source of randomness
      var maybeNonceSalt := cryptoPrimitives.GenerateRandomBytes(
        Crypto.GenerateRandomBytesInput(length := H_WRAP_NONCE_LEN + H_WRAP_SALT_LEN)
      );
      var saltAndNonce :- maybeNonceSalt.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      
      var salt := saltAndNonce[0..H_WRAP_SALT_LEN];
      var nonce := saltAndNonce[H_WRAP_SALT_LEN..];
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping-and-unwrapping-aad
      //# the keyring MUST include the following values as part of the AAD for the AES Encrypt/Decrypt calls.
      // (blank line for duvet)
      // To construct the AAD, the keyring MUST concatante the following values
      // (blank line for duvet)
      //# 1. "aws-kms-hierarchy" as UTF8 Bytes
      //# 1. Value of `branch-key-id` as UTF8 Bytes
      //# 1. [version](../structures.md#branch-key-version) as Bytes
      //# 1. [encryption context](structures.md#encryption-context-1) from the input
      //#   [encryption materials](../structures.md#encryption-materials) in the same format as the serialization of
      //#   [message header AAD key value pairs](../../data-format/message-header.md#key-value-pairs).
      var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersion, aad);
      
      var wrappedPdk :- BranchKeyWrapping(hierarchicalMaterials, plaintextDataKey, nonce, salt, wrappingAad, cryptoPrimitives);

      // TODO above we wrapped a key according to the standard ESDK Hierarchy Spec
      // For DBE we have to perform additional wrapping - coming in a followup PR
      // TODO decode branchKeyVersion to get the plain bytes here instead of the UTF8 Bytes
      var serializedEdk := salt + nonce + branchKeyVersion + wrappedPdk.cipherText + wrappedPdk.authTag;

      var edk := Types.EncryptedDataKey(
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //= type=implication
        //# [key provider id](../structures.md#key-provider-id): MUST be UTF8 Encoded "aws-kms-hierarchy"
        keyProviderId := PROVIDER_ID_HIERARCHY,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //= type=implication
        //# [key provider info](../structures.md#key-provider-information): MUST be the UTF8 Encoded AWS DDB response `branch-key-id`
        keyProviderInfo := branchKeyIdUtf8,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //= type=implication
        //# [ciphertext](../structures.md#ciphertext): MUST be serialized as the [hierarchical keyring ciphertext](#ciphertext)
        ciphertext := serializedEdk
      );

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
      //= type=implication
      //# OnEncrypt MUST append a new [encrypted data key](../structures.md#encrypted-data-key)
      //# to the encrypted data key list in the [encryption materials](../structures.md#encryption-materials)
      :- Need(
        // TODO add support
        materials.algorithmSuite.symmetricSignature.None?,
        E("Symmetric Signatures not yet implemented.")
      );

      var nextMaterials :- if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk], None)
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk], None);
      var result := Types.OnEncryptOutput(materials := nextMaterials);
      return Success(result);
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
      var materials := input.materials;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        E("Keyring received decryption materials that already contain a plaintext data key.")
      );
      
      var filter := new OnDecryptHierarchyEncryptedDataKeyFilter(branchKeyId);
      var edksToAttempt :- FilterWithResult(filter, input.encryptedDataKeys);

      :- Need(
        0 < |edksToAttempt|,
        E("Unable to decrypt data key: No Encrypted Data Keys found to match.")
      );
    
      var aad :- EncryptionContextToAADHierarchy(materials.encryptionContext);
      var decryptClosure := new DecryptSingleEncryptedDataKey(
        materials,
        aad,
        kmsClient,
        ddbClient,
        cryptoPrimitives,
        branchKeyStoreName,
        branchKeyId,
        awsKmsKey,
        grantTokens
      );

      var outcome, attempts := ReduceToSuccess(
        decryptClosure,
        edksToAttempt
      );

      var SealedDecryptionMaterials :- outcome
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
        //# If OnDecrypt fails to successfully decrypt any [encrypted data key]
        //# (../structures.md#encrypted-data-key), then it MUST yield an error
        //# that includes all the collected errors.
        .MapFailure(errors => Types.CollectionOfErrors( list := errors));
      
      assert decryptClosure.Ensures(Last(attempts).input, Success(SealedDecryptionMaterials), DropLast(attempts));
      return Success(Types.OnDecryptOutput(
        materials := SealedDecryptionMaterials
      ));
    }

    method GetActiveHierarchicalMaterials(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>
    )
      returns (material: Result<Types.HierarchicalMaterials, Types.Error>)
      requires ValidState()
      modifies ddbClient.Modifies, kmsClient.Modifies, cryptoPrimitives.Modifies
      ensures ValidState()
    {
      var expressionAttributeValues : DDB.AttributeMap := map[
        EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := DDB.AttributeValue.S(EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE),
        EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := DDB.AttributeValue.S(branchKeyId)
      ];

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
      //= type=implication
      //# To query this keystore, the caller MUST do the following:
      var queryInput := DDB.QueryInput(
        TableName := branchKeyStoreName,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
        //= type=implication
        //# To query this keystore, the caller MUST do the following:
        // (blank line for duvet)
        //# Use the global secondary index (GSI) Active-Keys to query the keystore to retrieve the active key 
        //# that matches the branch-key-id configured on the keyring. 
        IndexName := Some(BRANCH_KEY_STORE_GSI),
        Select := None(),
        AttributesToGet := None(),
        Limit := None(),
        ConsistentRead :=  None() ,
        KeyConditions := None(),
        QueryFilter := None(),
        ConditionalOperator := None(),
        ScanIndexForward := None(),
        ExclusiveStartKey := None(),
        ReturnConsumedCapacity :=  None(),
        ProjectionExpression := None(),
        FilterExpression := None(),
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

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
      //= type=implication
      //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../branch-key-store.md#record-format).
      //# If the record does not contain the defined fields, OnEncrypt MUST fail.
      :- Need(
        branchKeyItemHasRequiredAttributes?(queryResponse.Items.value[0]),
        E("Malformed Branch Key entry")
      );

      // TODO resolve the one to take by using the create-time value
      // if we have an active-active case we should resolve the version to use 
      // by looking at the `create-time` value
      var branchKeyRecord: branchKeyItem := queryResponse.Items.value[0];

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
      //= type=implication
      //# The keyring MUST use the configured `KMS SDK Client` to decrypt the value of the branch key field.
      var branchKeyResponse :- decryptBranchKey(branchKeyRecord, awsKmsKey, grantTokens, kmsClient);

      // TODO figure out how to validate a uuid
      // We should be able to convert this uuid string to the 16 byte representation      
      var branchKeyUuidString: string := branchKeyRecord["version"].S;
      var branchKeyUuidUtf8 :- UTF8.Encode(branchKeyUuidString)
        .MapFailure(WrapStringToError);
      
      var branchKey : seq<uint8> := branchKeyResponse.Plaintext.value;
      
      var hierarchicalMaterials := Types.HierarchicalMaterials(
        branchKey := branchKey,
        branchKeyVersion := branchKeyUuidUtf8
      );
      
      return Success(hierarchicalMaterials);
    }
  }

  method decryptBranchKey(
    branchKeyRecord: branchKeyItem,
    awsKmsKey: AwsKmsIdentifierString,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKeyManagementServiceClient
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
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
    //= type=implication
    //# The keyring MUST create a branch key [encryption context](../structures.md#encryption-context) map using
    //# each attribute name from the AWS DDB response except the `enc` attribute as a key and each corresponding
    //# attribute value as the value of the KMS Encryption Context.
    var wrappedBranchKey: KMS.CiphertextType := branchKeyRecord[BRANCH_KEY_FIELD].B;

    var encCtxDdbMap := branchKeyRecord - {BRANCH_KEY_FIELD};

    var encCtxMap: map<string, string> :=
      map k <- encCtxDdbMap ::
        k := ValueToString(encCtxDdbMap[k]).value; 
    
    var decryptRequest :=
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
      //= type=implication
      //# the keyring MUST call with a request constructed as follows: 
      KMS.DecryptRequest(
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
        //# - `KeyId` MUST be the configured AWS KMS key identifier.
        KeyId := Some(awsKmsKey),
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
        //# - `CiphertextBlob` MUST be the `enc` AWS DDB response value.
        CiphertextBlob := wrappedBranchKey,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
        //# - `EncryptionContext` MUST be the branch key encryption context map.
        EncryptionContext := Some(encCtxMap),
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
        //# - `GrantTokens` MUST be this keyring's
        //# [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
        GrantTokens := Some(grantTokens),
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
      case _ => Failure(Types.AwsCryptographicMaterialProvidersException(message := "Type not supported"))
    }
  }

  method DeriveEncryptionKeyFromBranchKey(
    branchKey: seq<uint8>,
    salt: seq<uint8>,
    purpose: Option<seq<uint8>>,
    cryptoPrimitives: Primitives.AtomicPrimitivesClient
  )
    returns (output: Result<seq<uint8>, Types.Error>)

    requires cryptoPrimitives.ValidState()
    modifies cryptoPrimitives.Modifies
    ensures cryptoPrimitives.ValidState()
    ensures output.Success? ==> |output.value| == 32
  {
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
    //# 3. Use a [KDF in Counter Mode with a Pseudo Random Function with HMAC SHA 256]
    //# (https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-108r1.pdf) 
    var maybeDerivedBranchKey := cryptoPrimitives.KdfCounterMode(
      Crypto.KdfCtrInput(
        digestAlgorithm := Crypto.DigestAlgorithm.SHA_256,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# - Use the branch key as the `key`.
        ikm := branchKey,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# to derive a 32 byte `derivedBranchKey`
        expectedLength := DERIVED_BRANCH_KEY_EXPECTED_LENGTH,
        // TODO: change name to label
        purpose := purpose,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# - Use the `salt` as the salt.
        nonce := Some(salt)
      )
    );
    var derivedBranchKey :- maybeDerivedBranchKey.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
    output := Success(derivedBranchKey);
  }

  method BranchKeyWrapping(
    hierarchicalMaterials: Types.HierarchicalMaterials,
    pdk: seq<uint8>,
    iv: seq<uint8>,
    salt: seq<uint8>,
    aad: seq<uint8>,
    cryptoPrimitives: Primitives.AtomicPrimitivesClient
  )
    returns (output: Result<Crypto.AESEncryptOutput, Types.Error>)
    requires cryptoPrimitives.ValidState()
    modifies cryptoPrimitives.Modifies
    ensures cryptoPrimitives.ValidState()
  {
    var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
      hierarchicalMaterials.branchKey,
      salt,
      Some(PROVIDER_ID_HIERARCHY),
      cryptoPrimitives
    );
    var maybeWrappedPdk := cryptoPrimitives.AESEncrypt(
      Crypto.AESEncryptInput(
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //= type=implication
        //# 1. Encrypt a plaintext data key with the `derivedBranchKey` using
        //# `AES-GCM-256` with the following inputs:
        encAlg := AES_256_ENC_ALG,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //= type=implication
        //# MUST use the derived `IV` as the AES-GCM IV.  
        iv := iv,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //= type=implication
        //# MUST use the `derivedBranchKey` as the AES-GCM cipher key.
        key := derivedBranchKey,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //= type=implication
        //# MUST use the plain text data key that will be wrapped by the `derivedBranchKey` as the AES-GCM message.
        msg := pdk ,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //= type=implication
        //# - MUST use the serialized [AAD](#branch-key-wrapping-and-unwrapping-aad) as the AES-GCM AAD.
        aad := aad
      )
    );
    var wrappedPdk :- maybeWrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
    output := Success(wrappedPdk);
  }

  method BranchKeyUnwrapping(
    hierarchicalMaterials: Types.HierarchicalMaterials,
    ciphertext: seq<uint8>,
    iv: seq<uint8>,
    salt: seq<uint8>,
    aad: seq<uint8>,
    authTag: seq<uint8>,
    cryptoPrimitives: Primitives.AtomicPrimitivesClient
  )
    returns (output: Result<seq<uint8>, Types.Error>)
    requires cryptoPrimitives.ValidState()
    modifies cryptoPrimitives.Modifies
    ensures cryptoPrimitives.ValidState()
  {
    var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
      hierarchicalMaterials.branchKey,
      salt,
      Some(PROVIDER_ID_HIERARCHY),
      cryptoPrimitives);
    var maybeUnwrappedPdk :=  cryptoPrimitives.AESDecrypt(
      Crypto.AESDecryptInput(
        encAlg := AES_256_ENC_ALG,
        key := derivedBranchKey,
        cipherTxt := ciphertext,
        authTag := authTag, 
        iv := iv,
        aad := aad
      )
    );
    var unwrappedPdk :- maybeUnwrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
    output := Success(unwrappedPdk);
  }

  //=  aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
  //# The keyring MUST attempt to serialize the [encryption materials']
  //# (structures.md#encryption-materials) [encryption context]
  //# (structures.md#encryption-context-1) in the same format as the
  //# serialization of [message header AAD key value pairs](../data-format/
  //# message-header.md#key-value-pairs).
  // TODO: Tests/proofs
  // TODO move to CanonicalEncryptionContext.dfy
  function method EncryptionContextToAADHierarchy(
    encryptionContext: Types.EncryptionContext
  ):
    (res: Result<seq<uint8>, Types.Error>)
  {
    :- Need(
      |encryptionContext| < UINT16_LIMIT,
      E("Encryption Context is too large")
    );
    var keys := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);

    if |keys| == 0 then
      // TODO: this adheres to spec (message-header.md) but diverges from what we do
      // in EncryptionContext.WriteAADSection
      Success([])
    else
      var KeyIntoPairBytes := k
        requires k in encryptionContext
      =>
        var v := encryptionContext[k];
        :- Need(
          HasUint16Len(k) && HasUint16Len(v),
          E("Unable to serialize encryption context")
        );
        Success(UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);

      var pairsBytes :- Seq.MapWithResult(KeyIntoPairBytes, keys);

      // The final return should be the bytes of the pairs, prepended with the number of pairs
      var allBytes := UInt16ToSeq(|keys| as uint16) + Seq.Flatten(pairsBytes);
      Success(allBytes)
  }

  method WrappingAad(
    branchKeyId: seq<uint8>,
    branchKeyVersion: seq<uint8>,
    aad: seq<uint8>
  )
    returns (res : seq<uint8>)
    requires UTF8.ValidUTF8Seq(branchKeyId)
    // TODO right now branchKeyVersion is stored as UTF8 Bytes in the materials
    // I either have to 1) decode the version every single time to get the raw uuid
    // or 2). store it as raw bytes in the materials so that I can encode it once per call.
  {
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping-and-unwrapping-aad
      //= type=implication
      //# To construct the AAD, the keyring MUST concatante the following values
      // (blank line for duvet)
      //# 1. "aws-kms-hierarchy" as UTF8 Bytes
      //# 1. Value of `branch-key-id` as UTF8 Bytes
      //# 1. [version](../structures.md#branch-key-version) as Bytes
      //# 1. [encryption context](structures.md#encryption-context-1) from the input
      //# [encryption materials](../structures.md#encryption-materials) in the same format as the serialization of
      //# [message header AAD key value pairs](../../data-format/message-header.md#key-value-pairs).
      var wraapingAad := PROVIDER_ID_HIERARCHY + branchKeyId + branchKeyVersion + aad;
      return wraapingAad;
  }
  
  class OnDecryptHierarchyEncryptedDataKeyFilter
    extends DeterministicActionWithResult<Types.EncryptedDataKey, bool, Types.Error>
  {
    const branchKeyId: string

    constructor(
      branchKeyId: string
    )
    {
      this.branchKeyId := branchKeyId;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<bool, Types.Error>
    ) {
      && (
          && res.Success?
          && res.value
        ==>
          edk.keyProviderId == PROVIDER_ID_HIERARCHY)
    }

    method Invoke(edk: Types.EncryptedDataKey)
      returns (res: Result<bool, Types.Error>)
      ensures Ensures(edk, res)
    {
      var providerInfo := edk.keyProviderInfo;
      var providerId := edk.keyProviderId;

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //= type=implication
      //# - Its provider ID MUST match the UTF8 Encoded value of “aws-kms-hierarchy”.
      if providerId != PROVIDER_ID_HIERARCHY {
        return Success(false);
      }
      
      if !UTF8.ValidUTF8Seq(providerInfo) {
        // The Keyring produces UTF8 keyProviderInfo.
        // If an `aws-kms-hierarchy` encrypted data key's keyProviderInfo is not UTF8
        // this is an error, not simply an EDK to filter out.
        return Failure(E("Invalid encoding, provider info is not UTF8."));
      }

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //# -- The deserialized key provider info MUST be UTF8 Decoded
      var branchKeyId :- UTF8.Decode(providerInfo).MapFailure(WrapStringToError);
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#ondecrypt
      //#  MUST match this keyring's configured `Branch Key Identifier`.
      return Success(this.branchKeyId == branchKeyId);
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      Types.EncryptedDataKey,
      Materials.SealedDecryptionMaterials,
      Types.Error>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const aad: seq<uint8>
    const kmsClient: KMS.IKeyManagementServiceClient
    const ddbClient: DDB.IDynamoDB_20120810Client
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const branchKeyStoreName: string
    const branchKeyId: string
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMS.GrantTokenList

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      aad: seq<uint8>,
      kmsClient: KMS.IKeyManagementServiceClient,
      ddbClient: DDB.IDynamoDB_20120810Client,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient,
      branchKeyStoreName: string,
      branchKeyId: string,
      awsKmsKey: AwsKmsIdentifierString,
      grantTokens: KMS.GrantTokenList
    )
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires DDB.IsValid_TableName(branchKeyStoreName)
      requires kmsClient.ValidState() && ddbClient.ValidState() && cryptoPrimitives.ValidState()
      ensures
      && this.materials == materials
      && this.aad       == aad
      && this.kmsClient == kmsClient
      && this.ddbClient == ddbClient
      && this.cryptoPrimitives == cryptoPrimitives
      && this.branchKeyStoreName     == branchKeyStoreName
      && this.branchKeyId == branchKeyId
      && this.awsKmsKey == awsKmsKey
      && this.grantTokens == grantTokens
      ensures Invariant()
    {
      this.materials := materials;
      this.aad       := aad;
      this.kmsClient := kmsClient;
      this.ddbClient := ddbClient;
      this.cryptoPrimitives := cryptoPrimitives;
      this.branchKeyStoreName := branchKeyStoreName;
      this.branchKeyId := branchKeyId;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
      Modifies := kmsClient.Modifies + ddbClient.Modifies + cryptoPrimitives.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && kmsClient.ValidState()
      && ddbClient.ValidState()
      && cryptoPrimitives.ValidState()
      && DDB.IsValid_TableName(this.branchKeyStoreName)
      && kmsClient.Modifies + ddbClient.Modifies + cryptoPrimitives.Modifies == Modifies
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<Materials.SealedDecryptionMaterials, Types.Error>,
      attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      // TODO look at the KMS keyring to see how we ensure that the call
      // to KMS was done correctly; this might be hard to prove once we add the cache
      // but we should be able to do it.
        res.Success?
      ==>
        && Invariant()
        && KMS.IsValid_CiphertextType(edk.ciphertext)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)

    }
    method Invoke(
      edk: Types.EncryptedDataKey,
      // aad: seq<uint8>,
      ghost attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    ) returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(edk, res, attemptsState)
    {
      :- Need (
        // Salt = 16, IV = 12, Version = 36, Encrypted Key = 32, Authentication Tag = 16
        && |edk.ciphertext| == EXPECTED_EDK_CIPHERTEXT_LENGTH
        && UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException(message := "Received EDK Ciphertext of incorrect length.")
      );

      var suite := materials.algorithmSuite;

      var keyProviderId := edk.keyProviderId;
      var branchKeyIdUtf8 := edk.keyProviderInfo;
      var ciphertext := edk.ciphertext;

      var salt := ciphertext[0..H_WRAP_SALT_LEN];
      var iv := ciphertext[H_WRAP_SALT_LEN..EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX];
      var branchKeyVersionUuid := ciphertext[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
      var wrappedKey := ciphertext[EDK_CIPHERTEXT_VERSION_INDEX..EDK_CIPHERTEXT_KEY_INDEX];
      var authTag := ciphertext[EDK_CIPHERTEXT_KEY_INDEX..];
      
      var hierarchicalMaterials :- GetHierarchicalMaterialsVersion(branchKeyId, branchKeyIdUtf8, branchKeyVersionUuid);
      var branchKey := hierarchicalMaterials.branchKey;
      var branchKeyVersionUtf8 := hierarchicalMaterials.branchKeyVersion;
      
      var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionUtf8, aad);
      var pdk :- BranchKeyUnwrapping(hierarchicalMaterials, wrappedKey, iv, salt, wrappingAad, authTag, cryptoPrimitives);

      :- Need(
        |pdk| == AES_256_ENC_KEY_LENGTH as int, 
        E("Unable to decrypt wrapped data key.")
      );
      
      // TODO add support
      :- Need(
        materials.algorithmSuite.symmetricSignature.None?,
        E("Symmetric Signatures not yet implemented.")
      );

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, pdk, None);
      return Success(result);
    }

    method GetHierarchicalMaterialsVersion(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>,
      branchKeyVersion: seq<uint8>
    )
      returns (material: Result<Types.HierarchicalMaterials, Types.Error>)
      // TODO Define valid HierarchicalMaterials such that we can ensure they are correct
      requires Invariant()
      requires ddbClient.ValidState() && kmsClient.ValidState() && cryptoPrimitives.ValidState()
      modifies ddbClient.Modifies, kmsClient.Modifies, cryptoPrimitives.Modifies
      ensures ddbClient.ValidState() && kmsClient.ValidState() && cryptoPrimitives.ValidState()
    {
      var version :- UTF8.Decode(branchKeyVersion).MapFailure(WrapStringToError);

      var dynamoDbKey: DDB.Key := map[
        BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(branchKeyId),
        VERSION_FIELD := DDB.AttributeValue.S(version)
      ];

      var ItemRequest := DDB.GetItemInput(
        Key := dynamoDbKey,
        TableName := branchKeyStoreName,
        AttributesToGet := None(),
        ConsistentRead :=  None(),
        ReturnConsumedCapacity := None(),
        ProjectionExpression := None(),
        ExpressionAttributeNames := None() 
      );

      var maybeGetItem := ddbClient.GetItem(ItemRequest);
      var getItemResponse :- maybeGetItem
        .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
      
      :- Need(
        getItemResponse.Item.Some?,
        E("No item found for corresponding branch key identifier.")
      );

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
      //= type=implication
      //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../branch-key-store.md#record-format).
      //# If the record does not contain the defined fields, OnEncrypt MUST fail.
      :- Need(
        branchKeyItemHasRequiredAttributes?(getItemResponse.Item.value),
        E("Malformed Branch Key entry")
      );
 
      var branchKeyRecord: branchKeyItem := getItemResponse.Item.value;

      var maybeBranchKeyResponse := decryptBranchKey(branchKeyRecord, awsKmsKey, grantTokens, kmsClient);
      var branchKeyResponse :- maybeBranchKeyResponse;

      var branchKeyUuidString: string := branchKeyRecord[VERSION_FIELD].S;
      var branchKeyUuid :- UTF8.Encode(branchKeyUuidString)
        .MapFailure(WrapStringToError);
      
      var branchKey : seq<uint8> := branchKeyResponse.Plaintext.value;
      
      var hierarchicalMaterials := Types.HierarchicalMaterials(
        branchKey := branchKey, 
        branchKeyVersion := branchKeyUuid
      );
      
      return Success(hierarchicalMaterials);
    }

  }

  function method SerializeEDKCiphertext(encOutput: Crypto.AESEncryptOutput): (ciphertext: seq<uint8>) {
    encOutput.cipherText + encOutput.authTag
  }

  function method E(s : string) : Types.Error {
    Types.AwsCryptographicMaterialProvidersException(message := s)
  }

}
