// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "AlgorithmSuites.dfy"


/*
 * Contains methods and helpers for working with commitment policies
 */
module Commitment {
  import opened Wrappers
  import opened AwsCryptographyMaterialProvidersTypes
  import AlgorithmSuites

  /*
   * Validates that the given algorithm is allowed by the the given commitment policy
   * during encryption
   */
  function method ValidateCommitmentPolicyOnEncrypt(
    algorithm: AlgorithmSuiteId,
    commitmentPolicy: CommitmentPolicy
  ):
    (res: Outcome<Error>)

    // Failure: Commitment policy forbids encrypting with commitment but the
    // algorithm provides it
    //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-forbid-encrypt-allow-decrypt
    //= type=test
    //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of False
    ensures
      (
        && commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Fail?

    // Failure: Commitment policy requires encrypting with commitment but the
    // algorithm does not provide it
    ensures
      (
        && (
          //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-allow-decrypt
          //= type=test
          //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
          //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-require-decrypt
          //= type=test
          //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
        )
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Fail?

    // Success: Commitment policy requires encrypting with commitment and the
    // algorithm provides it
    ensures
      (
        && (
          //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-allow-decrypt
          //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
          //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-require-decrypt
          //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
        )
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Pass?

    // Success: Commitment policy forbids encrypting with commitment and the
    // algorithm does not provide it
    //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-forbid-encrypt-allow-decrypt
    //# - [Get Encryption Materials](./cmm-interface.md#get-encryption-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of False
    ensures
      (
        && commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Pass?
  {
    var suite := AlgorithmSuites.GetSuite(algorithm);
    if
      && commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
      && !suite.commitment.None?
    then
      Fail(InvalidAlgorithmSuiteInfoOnEncrypt(
        message := "Configuration conflict. Commitment policy requires only non-committing algorithm suites"))
    else if
      && (
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
          || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
         )
      && suite.commitment.None?
    then
      Fail(InvalidAlgorithmSuiteInfoOnEncrypt(
        message :="Configuration conflict. Commitment policy requires only committing algorithm suites"))
    else
      Pass
  }

  /*
   * Validates that the given algorithm is allowed by the the given commitment policy
   * during decryption
   */
  function method ValidateCommitmentPolicyOnDecrypt(
    algorithm: AlgorithmSuiteId,
    commitmentPolicy: CommitmentPolicy
  ):
    // Bool return type on success is somewhat arbitrary; mainly we care about
    // success/failure
    (res: Outcome<Error>)

    // Failure: Commitment policy requires decrypting with commitment but the
    // algorithm does not provide it
    //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-require-decrypt
    //= type=test
    //# - [Decrypt Materials](./cmm-interface.md#decrypt-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
    ensures
      (
        && commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Fail?

    // Success: Commitment policy requires decrypting with commitment and
    // our algorithm provides it
    //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-require-decrypt
    //# - [Decrypt Materials](./cmm-interface.md#decrypt-materials) MUST only support algorithm suites that have a [Key Commitment](./algorithm-suites.md#algorithm-suites-encryption-key-derivation-settings) value of True
    ensures
      (
        && commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Pass?

    // Success: Commitment policy does not require decrypting with commitment and
    // our algorithm does not provide it
    ensures
      (
        && (
            //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-forbid-encrypt-allow-decrypt
            //= type=implication
            //# - [Decrypt Materials](./cmm-interface.md#decrypt-materials) MUST support all algorithm suites
            || commitmentPolicy == CommitmentPolicy.ESDK(FORBID_ENCRYPT_ALLOW_DECRYPT)
            //= aws-encryption-sdk-specification/framework/commitment-policy.md#esdk-require-encrypt-allow-decrypt
            //= type=implication
            //# - [Decrypt Materials](./cmm-interface.md#decrypt-materials) MUST support all algorithm suites
            || commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_ALLOW_DECRYPT)
           )
      )
    ==>
      res.Pass?

  {
    var suite := AlgorithmSuites.GetSuite(algorithm);

    if
      && commitmentPolicy == CommitmentPolicy.ESDK(REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
      && suite.commitment.None?
    then
      Fail(InvalidAlgorithmSuiteInfoOnDecrypt(
        message :="Configuration conflict. Commitment policy requires only committing algorithm suites"))
    else
      Pass
  }
}
