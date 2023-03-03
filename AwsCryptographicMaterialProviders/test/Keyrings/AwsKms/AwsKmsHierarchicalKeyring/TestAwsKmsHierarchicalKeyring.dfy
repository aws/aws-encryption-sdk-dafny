// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/Index.dfy"
include "../../../TestUtils.dfy"


module TestAwsKmsHierarchicalKeyring {
  import Types = AwsCryptographyMaterialProvidersTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import MaterialProviders
  import opened TestUtils
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  method {:test} TestClientWithHierarchy()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var dynamodbClient :- expect DDB.DynamoDBClient();
    var ttl : int64 := (1 * 60000) * 10;
    // THIS IS A TESTING RESOURCE DO NOT USE IN A PRODUCTION ENVIRONMENT
    var keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
    var branchKeyStoreArn := "arn:aws:dynamodb:us-west-2:370957321024:table/HierarchicalKeyringTestTable";

    var hierarchyKeyringResult := mpl.CreateAwsKmsHierarchicalKeyring(
      Types.CreateAwsKmsHierarchicalKeyringInput(
        branchKeyId := "hierarchy-test-v1",
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
    
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        signingKey := None,
        verificationKey := None
      )
    );

    var encryptionMaterialsOut :- expect hierarchyKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );
    
    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext
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