// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module Defaults {
  import opened AwsCryptographyMaterialProvidersTypes

  /* Returns the default algorithm suite for the given commitment policy */
  function method GetAlgorithmSuiteForCommitmentPolicy(commitmentPolicy:CommitmentPolicy):
    (output: AlgorithmSuiteId)

    ensures
      commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
      ==>
      output == AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384)

    ensures
      || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
      || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
      ==>
      output == AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384)
  {
    match commitmentPolicy
      case ESDK(c) => (
        match c
          case FORBID_ENCRYPT_ALLOW_DECRYPT() => AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384)
          case _ => AlgorithmSuiteId.ESDK(ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384)
      )
  }
}