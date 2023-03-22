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
    var branchKeyId := "hierarchy-test-v1";
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var materials := GetTestMaterials(TEST_ESDK_ALG_SUITE_ID);
    BuildKeyringAndTestEndToEnd(materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId, ttl);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_ESDK_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    BuildKeyringAndTestEndToEnd(materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId, ttl);
  }

  method {:test} TestTwoActiveKeysESDKSuite() 
  { 
    // The HierarchicalKeyringTestTable has two active keys under the branchKeyId below.
    // They have "create-time" timestamps of: 2023-03-07T17:09Z and 2023-03-07T17:07Z
    // When sorting them lexicographically, we should be using 2023-03-07T17:09Z as the "newest" 
    // branch key since this timestamp is more recent.
    var branchKeyId := "hierarchy-test-active-active";
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var materials := GetTestMaterials(TEST_ESDK_ALG_SUITE_ID);
    BuildKeyringAndTestEndToEnd(materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId, ttl);
    
    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_ESDK_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    BuildKeyringAndTestEndToEnd(materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId, ttl);
  }

  method {:test} TestHierarchyClientDBESuite() {
    var branchKeyId := "hierarchy-test-v1";
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    BuildKeyringAndTestEndToEnd(materials, TEST_DBE_ALG_SUITE_ID, branchKeyId, ttl);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_DBE_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    BuildKeyringAndTestEndToEnd(materials, TEST_DBE_ALG_SUITE_ID, branchKeyId, ttl);
  }
  
  method {:test} TestTwoActiveKeysDBESuite() 
  { 
    // The HierarchicalKeyringTestTable has two active keys under the branchKeyId below.
    // They have "create-time" timestamps of: 2023-03-07T17:09Z and 2023-03-07T17:07Z
    // When sorting them lexicographically, we should be using 2023-03-07T17:09Z as the "newest" 
    // branch key since this timestamp is more recent.
    var branchKeyId := "hierarchy-test-active-active";
    var ttl : Types.PositiveLong := (1 * 60000) * 10;
    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    BuildKeyringAndTestEndToEnd(materials, TEST_DBE_ALG_SUITE_ID, branchKeyId, ttl);

    //Test with key in the materials
    var suite := AlgorithmSuites.GetSuite(TEST_DBE_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, _ => 0); // Key is Zero
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    BuildKeyringAndTestEndToEnd(materials, TEST_DBE_ALG_SUITE_ID, branchKeyId, ttl);
  }

  method BuildKeyringAndTestEndToEnd(
    encryptionMaterialsIn: Types.EncryptionMaterials,
    algorithmSuiteId: Types.AlgorithmSuiteId,
    branchKeyId: string,
    ttl: Types.PositiveLong 
  ) {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var dynamodbClient :- expect DDB.DynamoDBClient();

    var hierarchyKeyringResult := mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := branchKeyId,
        kmsKeyId := keyArn,
        kmsClient := kmsClient,
        ddbClient := dynamodbClient,
        branchKeyStoreArn := branchKeyStoreArn,
        ttlSeconds := ttl,
        maxCacheSize := Option.Some(10),
        grantTokens := Option.None
      )
    );
    
    expect hierarchyKeyringResult.Success?;
    var hierarchyKeyring := hierarchyKeyringResult.value;
    
    var encryptionMaterialsOut :- expect hierarchyKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
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
}
