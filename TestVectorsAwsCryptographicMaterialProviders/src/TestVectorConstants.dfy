// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "TestVectorsUtils.dfy"

module TestVectorConstants {
  import Types = AwsCryptographyMaterialProvidersTypes
  import TestVectorsUtils

  datatype EncryptDecryptKeyrings =
    | AwsKmsKeyring
    | AwsKmsMultiKeyring
    | AwsKmsMrkKeyring
    | AwsKmsMrkMultiKeyring
    | RawAesKeyring
    | RawRsaKeyring
  
  const AllEncryptDecryptKeyrings := [
    AwsKmsKeyring,
    AwsKmsMultiKeyring,
    AwsKmsMrkKeyring,
    AwsKmsMrkMultiKeyring,
    RawAesKeyring,
    RawRsaKeyring
  ]

  lemma AllEncryptDecryptKeyringsIsComplete(i: EncryptDecryptKeyrings)
    ensures AllSeqIsComplete(i, AllEncryptDecryptKeyrings)
  {}

  const AllAwsKMSKeys := [
    ("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f", "us-west-2")
  ]

  const AllESDKAlgorithmSuiteIds := [
    Types.ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
    Types.ALG_AES_192_GCM_IV12_TAG16_NO_KDF,
    Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF,
    Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256,
    Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256,
    Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256,
    Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
    Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
    Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
    Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
  ]
  lemma AllESDKAlgorithmSuiteIdsIsComplete(i: Types.ESDKAlgorithmSuiteId)
    ensures AllSeqIsComplete(i, AllESDKAlgorithmSuiteIds)
  {}

  const AllDBEAlgorithmSuiteIds := [
    Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384,
	  Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384
  ];
  lemma AllDBEAlgorithmSuiteIdsIsComplete(i: Types.DBEAlgorithmSuiteId)
    ensures AllSeqIsComplete(i, AllDBEAlgorithmSuiteIds)
  {}

  const AllAlgorithmSuiteIds := [
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_NO_KDF),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_NO_KDF),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY),
    Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384)
    // Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384),
    // Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384)
  ]

  // lemma AllAlgorithmSuiteIdsIsComplete(i: Types.AlgorithmSuiteId)
  //   ensures AllSeqIsComplete(i, AllAlgorithmSuiteIds)
  // {
  //   match i {
  //     case ESDK(e) => AllESDKAlgorithmSuiteIdsIsComplete(e);
  //     case DBE(e) => AllDBEAlgorithmSuiteIdsIsComplete(e);
  //   }
  // }

  // Helper to prove that a seq is a complete
  // representation of all the possible types
  predicate AllSeqIsComplete<T>(i: T, all: seq<T>)
  {
    && i in all
    && (forall i: nat, j: nat
      | 0 <= i < j < |all|
      :: all[i] != all[j])
  }

}