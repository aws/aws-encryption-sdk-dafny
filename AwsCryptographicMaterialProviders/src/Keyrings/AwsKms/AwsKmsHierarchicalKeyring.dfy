// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../CanonicalEncryptionContext.dfy"
include "../../KeyWrapping/EdkWrapping.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsUtils.dfy"
include "../../CMCs/LocalCMC.dfy"

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
  import opened L = LocalCMC
  import opened AlgorithmSuites
  import EdkWrapping
  import MaterialWrapping
  import CanonicalEncryptionContext
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
  import UUID
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

  const EXPECTED_EDK_CIPHERTEXT_LENGTH := 92;
  const EDK_CIPHERTEXT_VERSION_LENGTH: int32 := 16;
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

  // We add this axiom here because verifying the mutability of the share state of the 
  // cache. Dafny does not support concurrency and proving the state of mutable frames 
  // is complicated.  
  lemma {:axiom} verifyValidStateCache (cmc: LocalCMC) ensures cmc.ValidState()

  method getEntry(cmc: LocalCMC, input: Types.GetCacheEntryInput) returns (res: Result<Types.GetCacheEntryOutput, Types.Error>)
    requires cmc.ValidState()
    ensures cmc.ValidState()
    ensures cmc.GetCacheEntryEnsuresPublicly(input, res)
    ensures unchanged(cmc.History)
  {
    // Because of the mutable state of the cache you may not know if you have an entry in cache 
    // at this point in execution; assuming we have not modified it allows dafny to verify that it can get an entry.
    assume {:axiom} cmc.Modifies == {};
    res := cmc.GetCacheEntry(input);
  }

  method putEntry(cmc: LocalCMC, input: Types.PutCacheEntryInput) returns (res: Result<(), Types.Error>)
    requires cmc.ValidState()
    ensures cmc.ValidState()
    ensures cmc.PutCacheEntryEnsuresPublicly(input, res)
    ensures unchanged(cmc.History)
  {
    // Because of the mutable state of the cache you may not know if you have an entry in cache 
    // at this point in execution; assuming we have not modified it allows dafny to verify that it can put an entry.
    assume {:axiom} cmc.Modifies == {};
    res := cmc.PutCacheEntry(input);
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
    const ttlSeconds: Types.PositiveLong
    const maxCacheSize: Types.PositiveInteger
    const grantTokens: KMS.GrantTokenList
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const branchKeyStoreIndex: string
    const cache: LocalCMC

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
      ttlSeconds: Types.PositiveLong,
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
      requires ttlSeconds >= 0
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
      var cmc := new LocalCMC(maxCacheSize as nat, 1);

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
      this.cache               := cmc;
      
      History := new Types.IKeyringCallHistory();
      Modifies := {History} + kmsClient.Modifies + ddbClient.Modifies + cryptoPrimitives.Modifies;
    }


    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}
    
    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials]
    //# (../structures.md#encryption-materials) as input.
    method {:vcs_split_on_every_assert} OnEncrypt'(input: Types.OnEncryptInput)
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
      
      var branchKeyIdUtf8 :- UTF8.Encode(this.branchKeyId)
        .MapFailure(WrapStringToError);
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
      //# The hierarchical keyring MUST attempt to obtain the hierarchical materials by querying 
      //# the backing branch keystore
      var hierarchicalMaterials :- GetActiveHierarchicalMaterials(branchKeyId, branchKeyIdUtf8);
      // TODO only pass in the branch key id
      
      var branchKey := hierarchicalMaterials.branchKey;
      var branchKeyVersion := hierarchicalMaterials.branchKeyVersion;
      var branchKeyVersionAsString :- UTF8.Decode(branchKeyVersion).MapFailure(WrapStringToError);
      var branchKeyVersionAsBytes :- UUID.ToByteArray(branchKeyVersionAsString).MapFailure(WrapStringToError);

      var kmsHierarchyGenerateAndWrap := new KmsHierarchyGenerateAndWrapKeyMaterial(
        hierarchicalMaterials.branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        cryptoPrimitives
      );
      var kmsHierarchyWrap := new KmsHierarchyWrapKeyMaterial(
        hierarchicalMaterials.branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        cryptoPrimitives
      );
      
      var wrapOutput :- EdkWrapping.WrapEdkMaterial<HierarchyWrapInfo>(
        encryptionMaterials := materials,
        wrap := kmsHierarchyWrap,
        generateAndWrap := kmsHierarchyGenerateAndWrap
      );

      var symmetricSigningKeyList :=
        if wrapOutput.symmetricSigningKey.Some? then
          Some([wrapOutput.symmetricSigningKey.value])
        else
          None;

      var edk := Types.EncryptedDataKey(
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [key provider id](../structures.md#key-provider-id): MUST be UTF8 Encoded "aws-kms-hierarchy"
        keyProviderId := PROVIDER_ID_HIERARCHY,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [key provider info](../structures.md#key-provider-information): MUST be the UTF8 Encoded AWS DDB response `branch-key-id`
        keyProviderInfo := branchKeyIdUtf8,
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# [ciphertext](../structures.md#ciphertext): MUST be serialized as the [hierarchical keyring ciphertext](#ciphertext)
        ciphertext := wrapOutput.wrappedMaterial
      );

      if (wrapOutput.GenerateAndWrapEdkMaterialOutput?) {
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#onencrypt
        //# OnEncrypt MUST append a new [encrypted data key](../structures.md#encrypted-data-key)
        //# to the encrypted data key list in the [encryption materials](../structures.md#encryption-materials)
        var result :- Materials.EncryptionMaterialAddDataKey(materials, wrapOutput.plaintextDataKey, [edk], symmetricSigningKeyList);
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      } else if (wrapOutput.WrapOnlyEdkMaterialOutput?) {
        var result :- Materials.EncryptionMaterialAddEncryptedDataKeys(
          materials,
          [edk],
          symmetricSigningKeyList
        );
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      }
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
    
      var decryptClosure := new DecryptSingleEncryptedDataKey(
        materials,
        kmsClient,
        ddbClient,
        cryptoPrimitives,
        branchKeyStoreName,
        branchKeyId,
        awsKmsKey,
        grantTokens,
        ttlSeconds,
        cache
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

    method GetActiveCacheId(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      returns (cacheId: Result<seq<uint8>, Types.Error>)

      requires cryptoPrimitives.ValidState()
      modifies cryptoPrimitives.Modifies
      ensures cryptoPrimitives.ValidState()
      ensures cacheId.Success? ==> |cacheId.value| == 32
    {
      :- Need(
        && UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).Success?
        && var branchKeyId := UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).value;
        && 0 <= |branchKeyId| < UINT32_LIMIT,
        E("Invalid Branch Key ID Length")
      );

      var branchKeyId := UTF8.Decode(branchKeyIdUtf8).value;
      var lenBranchKey := UInt.UInt32ToSeq(|branchKeyId| as uint32);

      var hashAlgorithm := Crypto.DigestAlgorithm.SHA_512;

      var maybeBranchKeyDigest := cryptoPrimitives
        .Digest(Crypto.DigestInput(digestAlgorithm := hashAlgorithm, message := branchKeyIdUtf8));
      var branchKeyDigest :- maybeBranchKeyDigest
        .MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      var activeUtf8 :- UTF8.Encode(EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE)
        .MapFailure(WrapStringToError);
      var identifier := lenBranchKey + branchKeyDigest + [0x00] + activeUtf8;

      var maybeCacheIdDigest := cryptoPrimitives
        .Digest(Crypto.DigestInput(digestAlgorithm := hashAlgorithm, message := identifier));
      var cacheDigest :- maybeCacheIdDigest
        .MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      :- Need(
        |cacheDigest| == Digest.Length(hashAlgorithm),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Digest generated a message not equal to the expected length.")
      );

      return Success(cacheDigest[0..32]);
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
      var cacheId :- GetActiveCacheId(branchKeyId, branchKeyIdUtf8, cryptoPrimitives);

      // call cache
      var getCacheInput := Types.GetCacheEntryInput(identifier := cacheId, bytesUsed := None);
      verifyValidStateCache(cache);
      var getCacheOutput := getEntry(cache, getCacheInput);

      if getCacheOutput.Failure? {
        var expressionAttributeValues : DDB.AttributeMap := map[
          EXPRESSION_ATTRIBUTE_VALUE_STATUS_KEY := DDB.AttributeValue.S(EXPRESSION_ATTRIBUTE_VALUE_STATUS_VALUE),
          EXPRESSION_ATTRIBUTE_VALUE_BRANCH_KEY := DDB.AttributeValue.S(branchKeyId)
        ];
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
        //# To query this keystore, the caller MUST do the following:
        var queryInput := DDB.QueryInput(
          TableName := branchKeyStoreName,
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
          //# To query this keystore, the caller MUST do the following:
          // (blank line for duvet)
          //# Use the global secondary index (GSI) Active-Keys to query the keystore to retrieve the active key 
          //# that matches the branch-key-id configured on the keyring. 
          IndexName := Some(BRANCH_KEY_STORE_GSI),
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

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#query-branch-keystore-onencrypt
        //# The AWS DDB response MUST contain the fields defined in the [branch keystore record format](../branch-key-store.md#record-format).
        //# If the record does not contain the defined fields, OnEncrypt MUST fail.
        :- Need(
          forall resp <- queryResponse.Items.value :: branchKeyItemHasRequiredAttributes?(resp),
          E("Malformed Branch Key entry")
        );

        // TODO resolve the one to take by using the create-time value
        // if we have an active-active case we should resolve the version to use 
        // by looking at the `create-time` value
        var branchKeyRecord := SortByTime(queryResponse.Items.value);

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#aws-kms-branch-key-decryption
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
        
        var now := Time.GetCurrent();

        var putCacheEntryInput:= Types.PutCacheEntryInput(
          identifier := cacheId,
          materials := Types.Materials.Hierarchical(hierarchicalMaterials),
          creationTime := now,
          expiryTime := ttlSeconds,
          messagesUsed := None,
          bytesUsed := None
        );

        verifyValidStateCache(cache);
        var _ :- putEntry(cache, putCacheEntryInput);

        return Success(hierarchicalMaterials);
      } else {
        :- Need(
          && getCacheOutput.value.materials.Hierarchical?
          && getCacheOutput.value.materials == Types.Materials.Hierarchical(getCacheOutput.value.materials.Hierarchical),
          E("Invalid Material Type.")
        );
        return Success(getCacheOutput.value.materials.Hierarchical);
      }
    }
  }

  method SortByTime(queryResponse: DDB.ItemList)
    returns (output: branchKeyItem)
    requires |queryResponse| > 0
    requires 
      && (forall resp <- queryResponse :: 
        && branchKeyItemHasRequiredAttributes?(resp))
    ensures branchKeyItemHasRequiredAttributes?(output)
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
      }
    }

    return newestBranchKey;
  }

  function method CharGreater(a: char, b: char): bool 
  {
    a > b
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
    ensures |cryptoPrimitives.History.GenerateRandomBytes| == old(|cryptoPrimitives.History.GenerateRandomBytes|)
    ensures |cryptoPrimitives.History.KdfCounterMode| > 0
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

  function method WrappingAad(
    branchKeyId: seq<uint8>,
    branchKeyVersion: seq<uint8>,
    aad: seq<uint8>
  ): (res : seq<uint8>)
    requires UTF8.ValidUTF8Seq(branchKeyId)
    // TODO right now branchKeyVersion is stored as UTF8 Bytes in the materials
    // I either have to 1) decode the version every single time to get the raw uuid
    // or 2). store it as raw bytes in the materials so that I can encode it once per call.
  {
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping-and-unwrapping-aad
      //# To construct the AAD, the keyring MUST concatante the following values
      // (blank line for duvet)
      //# 1. "aws-kms-hierarchy" as UTF8 Bytes
      //# 1. Value of `branch-key-id` as UTF8 Bytes
      //# 1. [version](../structures.md#branch-key-version) as Bytes
      //# 1. [encryption context](structures.md#encryption-context-1) from the input
      //# [encryption materials](../structures.md#encryption-materials) in the same format as the serialization of
      //# [message header AAD key value pairs](../../data-format/message-header.md#key-value-pairs).
      PROVIDER_ID_HIERARCHY + branchKeyId + branchKeyVersion + aad
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
    const kmsClient: KMS.IKeyManagementServiceClient
    const ddbClient: DDB.IDynamoDB_20120810Client
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient
    const branchKeyStoreName: string
    const branchKeyId: string
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMS.GrantTokenList
    const ttlSeconds: Types.PositiveLong
    const cache: L.LocalCMC

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      kmsClient: KMS.IKeyManagementServiceClient,
      ddbClient: DDB.IDynamoDB_20120810Client,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient,
      branchKeyStoreName: string,
      branchKeyId: string,
      awsKmsKey: AwsKmsIdentifierString,
      grantTokens: KMS.GrantTokenList,
      ttlSeconds: Types.PositiveLong,
      cache: L.LocalCMC
    )
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires DDB.IsValid_TableName(branchKeyStoreName)
      requires kmsClient.ValidState() && ddbClient.ValidState() && cryptoPrimitives.ValidState()
      ensures
      && this.materials == materials
      && this.kmsClient == kmsClient
      && this.ddbClient == ddbClient
      && this.cryptoPrimitives == cryptoPrimitives
      && this.branchKeyStoreName     == branchKeyStoreName
      && this.branchKeyId == branchKeyId
      && this.awsKmsKey == awsKmsKey
      && this.grantTokens == grantTokens
      && this.ttlSeconds == ttlSeconds
      && this.cache == cache
      ensures Invariant()
    {
      this.materials := materials;
      this.kmsClient := kmsClient;
      this.ddbClient := ddbClient;
      this.cryptoPrimitives := cryptoPrimitives;
      this.branchKeyStoreName := branchKeyStoreName;
      this.branchKeyId := branchKeyId;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
      this.ttlSeconds := ttlSeconds;
      this.cache := cache;
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
      ghost attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    ) returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(edk, res, attemptsState)
    {
      :- Need (
        UTF8.ValidUTF8Seq(edk.keyProviderInfo),
        Types.AwsCryptographicMaterialProvidersException(message := "Received invalid EDK provider info for Hierarchical Keyring")
      );

      var suite := materials.algorithmSuite;
      var keyProviderId := edk.keyProviderId;
      var branchKeyIdUtf8 := edk.keyProviderInfo;
      var ciphertext := edk.ciphertext;

      var providerWrappedMaterial :- EdkWrapping.GetProviderWrappedMaterial(ciphertext, suite);
      :- Need (
        |providerWrappedMaterial| >= EDK_CIPHERTEXT_VERSION_INDEX as nat,
        Types.AwsCryptographicMaterialProvidersException(message := "Received EDK Ciphertext of incorrect length.")
      );
      var branchKeyVersionUuid := providerWrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
      var hierarchicalMaterials :- GetHierarchicalMaterialsVersion(branchKeyId, branchKeyIdUtf8, branchKeyVersionUuid);
      var branchKey := hierarchicalMaterials.branchKey;
      var branchKeyVersion := hierarchicalMaterials.branchKeyVersion;
      var branchKeyVersionAsString :- UTF8.Decode(branchKeyVersion).MapFailure(WrapStringToError);
      var branchKeyVersionAsBytes :- UUID.ToByteArray(branchKeyVersionAsString).MapFailure(WrapStringToError);

      // We need to create a new client here so that we can reason about the state of the client
      // down the line. This is ok because the only state tracked is the client's history.
      var maybeCrypto := Primitives.AtomicPrimitives();
      var crypto :- maybeCrypto
        .MapFailure(e => Types.AwsCryptographyPrimitives(e));

      var kmsHierarchyUnwrap := new KmsHierarchyUnwrapKeyMaterial(
        branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        crypto
      );
      
      var unwrapOutputRes := EdkWrapping.UnwrapEdkMaterial(
          edk.ciphertext,
          materials,
          kmsHierarchyUnwrap
      ); 

      var unwrapOutput :- unwrapOutputRes; 

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, unwrapOutput.plaintextDataKey, unwrapOutput.symmetricSigningKey);
      return Success(result);
    }

     method GetVersionCacheId(
      branchKeyIdUtf8: seq<uint8>, // The branch key as Bytes
      branchKeyVersion: string,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      returns (cacheId: Result<seq<uint8>, Types.Error>)
      ensures cacheId.Success? ==> |cacheId.value| == 32
    {
      :- Need(
        && UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).Success?
        && var branchKeyId := UTF8.Decode(branchKeyIdUtf8).MapFailure(WrapStringToError).value;
        && 0 <= |branchKeyId| < UINT32_LIMIT,
        E("Invalid Branch Key ID Length")
      );

      var branchKeyId := UTF8.Decode(branchKeyIdUtf8).value;
      var lenBranchKey := UInt.UInt32ToSeq(|branchKeyId| as uint32);
      :- Need(
        UTF8.IsASCIIString(branchKeyVersion),
        E("Unable to represent as an ASCII string.")
      );
      var versionBytes := UTF8.EncodeAscii(branchKeyVersion);

      var identifier := lenBranchKey + branchKeyIdUtf8 + [0x00 as uint8] + versionBytes;
      var identifierDigestInput := Crypto.DigestInput(
        digestAlgorithm := Crypto.DigestAlgorithm.SHA_512, message := identifier
      );
      var maybeCacheDigest := Digest.Digest(identifierDigestInput);
      var cacheDigest :- maybeCacheDigest.MapFailure(e => Types.AwsCryptographyPrimitives(e));

      return Success(cacheDigest[0..32]);
    }

    method GetHierarchicalMaterialsVersion(
      branchKeyId: string,
      branchKeyIdUtf8: seq<uint8>,
      branchKeyVersion: seq<uint8>
    )
      returns (material: Result<Types.HierarchicalMaterials, Types.Error>)
      // TODO Define valid HierarchicalMaterials such that we can ensure they are correct
      requires |branchKeyVersion| == 16
      requires Invariant()
      requires ddbClient.ValidState() && kmsClient.ValidState() && cryptoPrimitives.ValidState()
      modifies ddbClient.Modifies, kmsClient.Modifies, cryptoPrimitives.Modifies
      ensures ddbClient.ValidState() && kmsClient.ValidState() && cryptoPrimitives.ValidState()
    {
      var version :- UUID.FromByteArray(branchKeyVersion).MapFailure(WrapStringToError);
      
      var cacheId :- GetVersionCacheId(branchKeyIdUtf8, version, cryptoPrimitives);
      // call cache
      var getCacheInput := Types.GetCacheEntryInput(identifier := cacheId, bytesUsed := None);
      verifyValidStateCache(cache);
      var getCacheOutput := getEntry(cache, getCacheInput);

      if getCacheOutput.Failure? {
        var dynamoDbKey: DDB.Key := map[
          BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(branchKeyId),
          VERSION_FIELD := DDB.AttributeValue.S(version)
        ];

        var ItemRequest := DDB.GetItemInput(
          Key := dynamoDbKey,
          TableName := branchKeyStoreName,
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
        
        var now := Time.GetCurrent();

        var putCacheEntryInput:= Types.PutCacheEntryInput(
          identifier := cacheId,
          materials := Types.Materials.Hierarchical(hierarchicalMaterials),
          creationTime := now,
          expiryTime := ttlSeconds, 
          messagesUsed := None,
          bytesUsed := None
        );

        verifyValidStateCache(cache);
        var _ :- putEntry(cache, putCacheEntryInput);

        return Success(hierarchicalMaterials);
      } else {
        :- Need(
          && getCacheOutput.value.materials.Hierarchical?
          && getCacheOutput.value.materials == Types.Materials.Hierarchical(getCacheOutput.value.materials.Hierarchical),
          E("Invalid Material Type.")
        );
        return Success(getCacheOutput.value.materials.Hierarchical);
      }
    }
  }

  datatype HierarchyUnwrapInfo = HierarchyUnwrapInfo()
  datatype HierarchyWrapInfo = HierarchyWrapInfo()
  
  class KmsHierarchyUnwrapKeyMaterial
    extends MaterialWrapping.UnwrapMaterial<HierarchyUnwrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
     constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8: UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
        && this.branchKey == branchKey
        && this.branchKeyIdUtf8 == branchKeyIdUtf8
        && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
        && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.UnwrapInput,
      res: Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && |input.wrappedMaterial| == EXPECTED_EDK_CIPHERTEXT_LENGTH
        && |crypto.History.AESDecrypt| > 0
        && Seq.Last(crypto.History.AESDecrypt).output.Success?
        && var AESDecryptInput := Seq.Last(crypto.History.AESDecrypt).input;
        && var AESDecryptOutput := Seq.Last(crypto.History.AESDecrypt).output.value;
        && var wrappedMaterial := input.wrappedMaterial;
        && var aad := input.encryptionContext;
        && var salt := wrappedMaterial[0..H_WRAP_SALT_LEN];
        && var iv := wrappedMaterial[H_WRAP_SALT_LEN..EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX];
        && var branchKeyVersionUuid := wrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
        && var wrappedKey := wrappedMaterial[EDK_CIPHERTEXT_VERSION_INDEX..EDK_CIPHERTEXT_KEY_INDEX];
        && var authTag := wrappedMaterial[EDK_CIPHERTEXT_KEY_INDEX..];
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && var serializedEC := CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).value;
        && var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);
        // Since we can't call a method here in the predicate we can't derive the key here
        // but we can make sure that the rest of the construction is correct.
        && AESDecryptInput.encAlg == AES_256_ENC_ALG
        && AESDecryptInput.cipherTxt == wrappedKey
        && AESDecryptInput.authTag == authTag
        && AESDecryptInput.iv == iv 
        && AESDecryptInput.aad == wrappingAad
        && AESDecryptOutput == res.value.unwrappedMaterial
    }
    
    method Invoke(
      input: MaterialWrapping.UnwrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.UnwrapOutput<HierarchyUnwrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==>
        |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      var suite := input.algorithmSuite;
      var wrappedMaterial := input.wrappedMaterial;
      var aad := input.encryptionContext;
      
      :- Need (
        // Salt = 16, IV = 12, Version = 16, Encrypted Key = 32, Authentication Tag = 16
        |wrappedMaterial| == EXPECTED_EDK_CIPHERTEXT_LENGTH,
        Types.AwsCryptographicMaterialProvidersException(message := "Received EDK Ciphertext of incorrect length.")
      );

      var salt := wrappedMaterial[0..H_WRAP_SALT_LEN];
      var iv := wrappedMaterial[H_WRAP_SALT_LEN..EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX];
      var branchKeyVersionUuid := wrappedMaterial[EDK_CIPHERTEXT_BRANCH_KEY_VERSION_INDEX..EDK_CIPHERTEXT_VERSION_INDEX];
      var wrappedKey := wrappedMaterial[EDK_CIPHERTEXT_VERSION_INDEX..EDK_CIPHERTEXT_KEY_INDEX];
      var authTag := wrappedMaterial[EDK_CIPHERTEXT_KEY_INDEX..];

      var serializedEC :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
      var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);
      var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
        branchKey,
        salt,
        Some(PROVIDER_ID_HIERARCHY),
        crypto
      );

      var maybeUnwrappedPdk :=  crypto.AESDecrypt(
        Crypto.AESDecryptInput(
          encAlg := AES_256_ENC_ALG,
          key := derivedBranchKey,
          cipherTxt := wrappedKey,
          authTag := authTag, 
          iv := iv,
          aad := wrappingAad
        )
      );
      var unwrappedPdk :- maybeUnwrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      :- Need(
        |unwrappedPdk| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat,
        E("Invalid Key Length")
      );

      var output := MaterialWrapping.UnwrapOutput(
        unwrappedMaterial := unwrappedPdk,
        unwrapInfo := HierarchyUnwrapInfo()
      );

      return Success(output);
    }
  }

  class KmsHierarchyGenerateAndWrapKeyMaterial
    extends MaterialWrapping.GenerateAndWrapMaterial<HierarchyWrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
    constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8 : UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
      && this.branchKey == branchKey
      && this.branchKeyIdUtf8 == branchKeyIdUtf8
      && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
      && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.GenerateAndWrapInput,
      res: Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) 
      reads Modifies
      decreases Modifies
    {
      res.Success?
        ==>
      && Invariant()
    }

    method Invoke(
      input: MaterialWrapping.GenerateAndWrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<HierarchyWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.plaintextMaterial| == input.algorithmSuite.encrypt.AES_GCM.keyLength as nat
    {
      var suite := input.algorithmSuite;
      var pdkResult := crypto
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(suite)));
      var pdk :- pdkResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e)); 

      var wrap := new KmsHierarchyWrapKeyMaterial(
        branchKey,
        branchKeyIdUtf8,
        branchKeyVersionAsBytes,
        crypto
      );

      var wrapOutput: MaterialWrapping.WrapOutput<HierarchyWrapInfo> :- wrap.Invoke(
        MaterialWrapping.WrapInput(
          plaintextMaterial := pdk,
          algorithmSuite := input.algorithmSuite,
          encryptionContext := input.encryptionContext
        ), []);

      var output := MaterialWrapping.GenerateAndWrapOutput(
        plaintextMaterial := pdk,
        wrappedMaterial := wrapOutput.wrappedMaterial,
        wrapInfo := HierarchyWrapInfo()
      );
      return Success(output);
    }

  }

  class KmsHierarchyWrapKeyMaterial
    extends MaterialWrapping.WrapMaterial<HierarchyWrapInfo>
  {
    const branchKey: seq<uint8>
    const branchKeyIdUtf8 : UTF8.ValidUTF8Bytes
    const branchKeyVersionAsBytes: seq<uint8>
    const crypto: Primitives.AtomicPrimitivesClient
    
    constructor(
      branchKey: seq<uint8>,
      branchKeyIdUtf8 : UTF8.ValidUTF8Bytes,
      branchKeyVersionAsBytes: seq<uint8>,
      crypto: Primitives.AtomicPrimitivesClient
    )
      requires crypto.ValidState()
      ensures
      && this.branchKey == branchKey
      && this.branchKeyIdUtf8 == branchKeyIdUtf8
      && this.branchKeyVersionAsBytes == branchKeyVersionAsBytes
      && this.crypto == crypto
      ensures Invariant()
    {
      this.branchKey := branchKey;
      this.branchKeyIdUtf8 := branchKeyIdUtf8;
      this.branchKeyVersionAsBytes := branchKeyVersionAsBytes;
      this.crypto := crypto;
      Modifies := crypto.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && crypto.ValidState()
      && crypto.Modifies == Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.WrapInput,
      res: Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && (
        res.Success?
          ==>
        && Invariant()
        && 0 < |crypto.History.AESEncrypt|
        && Seq.Last(crypto.History.AESEncrypt).output.Success?
        && var AESEncryptInput := Seq.Last(crypto.History.AESEncrypt).input;
        && var AESEncryptOutput := Seq.Last(crypto.History.AESEncrypt).output.value;
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && var serializedEC := CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
        && var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC.value);
        && AESEncryptInput.encAlg == AES_256_ENC_ALG 
        && AESEncryptInput.msg == input.plaintextMaterial
        && AESEncryptInput.aad == wrappingAad
        && |res.value.wrappedMaterial| > |AESEncryptOutput.cipherText| + |AESEncryptOutput.authTag|
        && res.value.wrapInfo == HierarchyWrapInfo()
      )
    }

    method Invoke(
      input: MaterialWrapping.WrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.WrapOutput<HierarchyWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      {
        var suite := input.algorithmSuite;

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
        //# The hierarchical keyring MUST:
        // (blank line for duvet)
        //# 1. Generate a 16 byte random salt using a secure source of randomness
        //# 1. Generate a 12 byte random iv using a secure source of randomness
        var maybeNonceSalt := crypto.GenerateRandomBytes(
          Crypto.GenerateRandomBytesInput(length := H_WRAP_SALT_LEN + H_WRAP_NONCE_LEN)
        );
        var saltAndNonce :- maybeNonceSalt.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
        
        assert |crypto.History.GenerateRandomBytes| == old(|crypto.History.GenerateRandomBytes|) + 1;
        assert |saltAndNonce| == (H_WRAP_NONCE_LEN + H_WRAP_SALT_LEN) as int;
        
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
        var serializedEC :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
        var wrappingAad := WrappingAad(branchKeyIdUtf8, branchKeyVersionAsBytes, serializedEC);

        var derivedBranchKey :- DeriveEncryptionKeyFromBranchKey(
          branchKey,
          salt,
          Some(PROVIDER_ID_HIERARCHY),
          crypto
        );

        var maybeWrappedPdk := crypto.AESEncrypt(
          Crypto.AESEncryptInput(
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# 1. Encrypt a plaintext data key with the `derivedBranchKey` using
            //# `AES-GCM-256` with the following inputs:
            encAlg := AES_256_ENC_ALG,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the derived `IV` as the AES-GCM IV.  
            iv := nonce,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the `derivedBranchKey` as the AES-GCM cipher key.
            key := derivedBranchKey,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# MUST use the plain text data key that will be wrapped by the `derivedBranchKey` as the AES-GCM message.
            msg := input.plaintextMaterial,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-hierarchical-keyring.md#branch-key-wrapping
            //# - MUST use the serialized [AAD](#branch-key-wrapping-and-unwrapping-aad) as the AES-GCM AAD.
            aad := wrappingAad
          )
        );
        var wrappedPdk :- maybeWrappedPdk.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

        var output := MaterialWrapping.WrapOutput(
          wrappedMaterial := salt + nonce +  branchKeyVersionAsBytes + wrappedPdk.cipherText + wrappedPdk.authTag,
          wrapInfo := HierarchyWrapInfo()
        );
        return Success(output);
      }
  }

  function method SerializeEDKCiphertext(encOutput: Crypto.AESEncryptOutput): (ciphertext: seq<uint8>) {
    encOutput.cipherText + encOutput.authTag
  }

  function method E(s : string) : Types.Error {
    Types.AwsCryptographicMaterialProvidersException(message := s)
  }

}
