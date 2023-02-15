// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module Defaults {
  import opened AwsCryptographyMaterialProvidersTypes

  /* Returns the default algorithm suite for the given commitment policy */
  function method GetAlgorithmSuiteForCommitmentPolicy(commitmentPolicy:CommitmentPolicy):
    (output: AlgorithmSuiteId)

    //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-forbid-encrypt-allow-decrypt
    //= type=implication
    //# - `ESDK.ALG_AES_256_GCM_IV12_TAG16_NO_KDF` MUST be the default algorithm suite
    ensures
      commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
      ==>
      output == AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384)

    ensures
      //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-allow-decrypt
      //= type=implication
      //# - `05 78` MUST be the default algorithm suite
      || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
      //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-require-decrypt
      //= type=implication
      //# - `05 78` MUST be the default algorithm suite
      || commitmentPolicy == CommitmentPolicy.ESDK(ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
      ==>
      output == AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384)

    ensures
      //= aws-encryption-sdk-specification/framework/commitment-policy.md#dbe-require-encrypt-require-decrypt
      //= type=implication
      //# - `67 01` MUST be the default algorithm suite
      commitmentPolicy == CommitmentPolicy.DBE(DBECommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
      ==>
      output == AlgorithmSuiteId.DBE(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384)
  {
    match commitmentPolicy
      case ESDK(c) => (
        match c
          case FORBID_ENCRYPT_ALLOW_DECRYPT() => AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384)
          case _ => AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384)
      )
      case DBE(_) => (
        AlgorithmSuiteId.DBE(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384)
      )
  }
}
