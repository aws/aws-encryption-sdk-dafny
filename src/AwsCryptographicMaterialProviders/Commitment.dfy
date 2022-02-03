// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "AlgorithmSuites.dfy"


/*
 * Contains methods and helpers for working with commitment policies
 */
module {:extern "Dafny.Aws.Crypto.MaterialProviders.Commitment"} MaterialProviders.Commitment {
  import opened Wrappers
  import Aws.Crypto
  import AlgorithmSuites

  /*
   * Validates that the given algorithm is allowed by the the given commitment policy
   * during encryption
   */
  function method ValidateCommitmentPolicyOnEncrypt(
    algorithm: Crypto.AlgorithmSuiteId,
    commitmentPolicy: Crypto.CommitmentPolicy
  ):
    // Bool return type on success is somewhat arbitrary; mainly we care about
    // success/failure
    (res: Result<bool, string>)

    // Failure: Commitment policy forbids encrypting with commitment but the
    // algorithm provides it
    ensures
      (
        && commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Failure?

    // Failure: Commitment policy requires encrypting with commitment but the
    // algorithm does not provide it
    ensures
      (
        && (
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        )
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Failure?

    // Success: Commitment policy requires encrypting with commitment and the
    // algorithm provides it
    ensures
      (
        && (
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        )
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Success?

    // Success: Commitment policy forbids encrypting with commitment and the
    // algorithm does not provide it
    ensures
      (
        && commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Success?
  {
    var suite := AlgorithmSuites.GetSuite(algorithm);
    if
      && commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
      && !suite.commitment.None?
    then
      Failure("Configuration conflict. Commitment policy requires only non-committing algorithm suites")
    else if
      && (
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
         )
      && suite.commitment.None?
    then
      Failure("Configuration conflict. Commitment policy requires only committing algorithm suites")
    else
      Success(true)
  }

  /*
   * Validates that the given algorithm is allowed by the the given commitment policy
   * during decryption
   */
  function method ValidateCommitmentPolicyOnDecrypt(
    algorithm: Crypto.AlgorithmSuiteId,
    commitmentPolicy: Crypto.CommitmentPolicy
  ):
    // Bool return type on success is somewhat arbitrary; mainly we care about
    // success/failure
    (res: Result<bool, string>)

    // Failure: Commitment policy requires decrypting with commitment but the
    // algorithm does not provide it
    ensures
      (
        && commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Failure?

    // Success: Commitment policy requires decrypting with commitment and
    // our algorithm provides it
    ensures
      (
        && commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && !suite.commitment.None?
      )
    ==>
      res.Success?

    // Success: Commitment policy does not require decrypting with commitment and
    // our algorithm does not provide it
    ensures
      (
        && (
            || commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
            || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
           )
        && var suite := AlgorithmSuites.GetSuite(algorithm);
        && suite.commitment.None?
      )
    ==>
      res.Success?

  {
    var suite := AlgorithmSuites.GetSuite(algorithm);

    if
      && commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
      && suite.commitment.None?
    then
      Failure("Configuration conflict. Commitment policy requires only committing algorithm suites")
    else
      Success(true)
  }
}
