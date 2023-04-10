// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/Index.dfy"
include "../../../TestUtils.dfy"
include "../../../../src/AlgorithmSuites.dfy"
include "../../../../src/Materials.dfy"


module TestAwsKmsHierarchicalKeyring {
  import Types = AwsCryptographyMaterialProvidersTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import Crypto = AwsCryptographyPrimitivesTypes
  import Aws.Cryptography.Primitives
  import MaterialProviders
  import opened TestUtils
  import opened AlgorithmSuites
  import opened Materials
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  const TEST_ESDK_ALG_SUITE_ID := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
  const TEST_DBE_ALG_SUITE_ID := Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384);
  // THIS IS A TESTING RESOURCE DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
  const branchKeyStoreArn := "arn:aws:dynamodb:us-west-2:370957321024:table/HierarchicalKeyringTestTable";

  // These tests require a keystore populated with these keys
  const BRANCH_KEY_ID := "hierarchy-test-v1";
  const ACTIVE_ACTIVE_BRANCH_KEY_ID := "hierarchy-test-active-active";

  // Constants for TestBranchKeySupplier
  const BRANCH_KEY := UTF8.EncodeAscii("branchKey");
  const CASE_A := UTF8.EncodeAscii("caseA");
  const CASE_B := UTF8.EncodeAscii("caseB");
  const BRANCH_KEY_ID_A := BRANCH_KEY_ID
  const BRANCH_KEY_ID_B := ACTIVE_ACTIVE_BRANCH_KEY_ID

  method GetTestMaterials(suiteId: Types.AlgorithmSuiteId) returns (out: Types.EncryptionMaterials) 
  {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var suite := AlgorithmSuites.GetSuite(suiteId);
    // Add data key to test the case wherer i have a pdk
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := suiteId,
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := [],
        signingKey := None,
        verificationKey := None
      )
    );

    return encryptionMaterialsIn;
  }
  
  method {:test} TestHierarchyClientESDKSuite()
  {
    var branchKeyId := BRANCH_KEY_ID;
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var kmsClient :- expect KMS.KMSClient();
    var mpl :- expect MaterialProviders.MaterialProviders();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := Some(branchKeyId),
        branchKeyIdSupplier := None,
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );

    var materials := GetTestMaterials(TEST_ESDK_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_ESDK_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);
  }

  method {:test} TestTwoActiveKeysESDKSuite() 
  { 
    // The HierarchicalKeyringTestTable has two active keys under the branchKeyId below.
    // They have "create-time" timestamps of: 2023-03-07T17:09Z and 2023-03-07T17:07Z
    // When sorting them lexicographically, we should be using 2023-03-07T17:09Z as the "newest" 
    // branch key since this timestamp is more recent.
    var branchKeyId := ACTIVE_ACTIVE_BRANCH_KEY_ID;
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var kmsClient :- expect KMS.KMSClient();
    var mpl :- expect MaterialProviders.MaterialProviders();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := Some(branchKeyId),
        branchKeyIdSupplier := None,
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );

    var materials := GetTestMaterials(TEST_ESDK_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);
    
    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_ESDK_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);
  }

  method {:test} TestHierarchyClientDBESuite() {
    var branchKeyId := BRANCH_KEY_ID;
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var kmsClient :- expect KMS.KMSClient();
    var mpl :- expect MaterialProviders.MaterialProviders();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := Some(branchKeyId),
        branchKeyIdSupplier := None,
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );

    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_DBE_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);
  }
  
  method {:test} TestTwoActiveKeysDBESuite() 
  { 
    // The HierarchicalKeyringTestTable has two active keys under the branchKeyId below.
    // They have "create-time" timestamps of: 2023-03-07T17:09Z and 2023-03-07T17:07Z
    // When sorting them lexicographically, we should be using 2023-03-07T17:09Z as the "newest" 
    // branch key since this timestamp is more recent.
    var branchKeyId := ACTIVE_ACTIVE_BRANCH_KEY_ID;
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var kmsClient :- expect KMS.KMSClient();
    var mpl :- expect MaterialProviders.MaterialProviders();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := Some(branchKeyId),
        branchKeyIdSupplier := None,
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );

    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_DBE_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);
  }


  method {:test} TestBranchKeyIdSupplier() 
  {
    var branchKeyIdSupplier: Types.IBranchKeyIdSupplier := new DummyBranchKeyIdSupplier(); 
    var ttl : int64 := (1 * 60000) * 10;
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := None,
        branchKeyIdSupplier := Some(branchKeyIdSupplier),
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );
    
    // Test Encryption Context with Case A
    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    var contextCaseA := materials.encryptionContext[BRANCH_KEY := CASE_A];
    materials := materials.(encryptionContext := contextCaseA);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, BRANCH_KEY_ID_A); 

    // Test Encryption Context with Case B
    var contextCaseB := materials.encryptionContext[BRANCH_KEY := CASE_B];
    materials := materials.(encryptionContext := contextCaseB);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, BRANCH_KEY_ID_B); 
  }

  method TestRoundtrip(
    hierarchyKeyring: Types.IKeyring,
    encryptionMaterialsIn: Types.EncryptionMaterials,
    algorithmSuiteId: Types.AlgorithmSuiteId,
    expectedBranchKeyId: string
  )
    requires hierarchyKeyring.ValidState()
    modifies hierarchyKeyring.Modifies
    ensures hierarchyKeyring.ValidState()
  {
    var encryptionMaterialsOut :- expect hierarchyKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    
    var mpl :- expect MaterialProviders.MaterialProviders();
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    
    // Verify the edk was created with the expected branch key
    var expectedBranchKeyIdUTF8 :- expect UTF8.Encode(expectedBranchKeyId);
    expect edk.keyProviderInfo == expectedBranchKeyIdUTF8;

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionMaterialsIn.encryptionContext,
        requiredEncryptionContextKeys := []
      )
    );
    var decryptionMaterialsOut :- expect hierarchyKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=test
    //# If a decryption succeeds, this keyring MUST add the resulting
    //# plaintext data key to the decryption materials and return the
    //# modified materials.
    expect encryptionMaterialsOut.materials.plaintextDataKey
    == decryptionMaterialsOut.materials.plaintextDataKey;
  }

  // Returns "hierarchy-test-v1" when EC contains kv pair "branchKey":"caseA"
  // Returns "hierarchy-test-active-active" when EC contains kv pair "branchKey":"caseB"
  // Otherwise returns a Failure
  class DummyBranchKeyIdSupplier extends Types.IBranchKeyIdSupplier
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      History in Modifies
    }

    constructor()
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies)
    {
      History := new Types.IBranchKeyIdSupplierCallHistory();
      Modifies := {History};
    }

    predicate GetBranchKeyIdEnsuresPublicly(input: Types.GetBranchKeyIdInput, output: Result<Types.GetBranchKeyIdOutput, Types.Error>)
    {true}

    method GetBranchKeyId'(input: Types.GetBranchKeyIdInput)
        returns (output: Result<Types.GetBranchKeyIdOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures GetBranchKeyIdEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      var context := input.encryptionContext;

      if BRANCH_KEY in context.Keys && context[BRANCH_KEY] == CASE_A {
        return Success(Types.GetBranchKeyIdOutput(branchKeyId:=BRANCH_KEY_ID_A));
      } else if BRANCH_KEY in context.Keys && context[BRANCH_KEY] == CASE_B {
        return Success(Types.GetBranchKeyIdOutput(branchKeyId:=BRANCH_KEY_ID_B));
      } else {
        return Failure(Types.AwsCryptographicMaterialProvidersException(message := "Can't determine branchKeyId from context"));
      }
    }
  }
}
