
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
  method ValidateCommitmentPolicyOnEncrypt(
    algorithm: Option<Crypto.AlgorithmSuiteId>,
    commitmentPolicy: Crypto.CommitmentPolicy
  )
    returns (res: Result<bool, string>)

    // If an algorithm suite was not provided it cannot conflict with the
    // commitment policy
    ensures algorithm.None? ==> res.Success?

    // Commitment policy forbids encrypting with commitment but the
    // algorithm provides it
    ensures
      (
        && commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
        && algorithm.Some?
        && var suite := AlgorithmSuites.GetSuite(algorithm.value);
        && !suite.commitment.None?
      )
    ==>
      res.Failure?

    // Commitment policy requires encrypting with commitment but the
    // algorithm does not provide it
    ensures
      (
        && (
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        )
        && algorithm.Some?
        && var suite := AlgorithmSuites.GetSuite(algorithm.value);
        && suite.commitment.None?
      )
    ==>
      res.Failure?
  {
    if algorithm.None? {
      return Success(true);
    }

    var suite := AlgorithmSuites.GetSuite(algorithm.value);

    if
      && commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
      && !suite.commitment.None?
    {
      return Failure("Configuration conflict. Commitment policy requires only non-committing algorithm suites");
    }

    if
      && (
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
          || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
         )
      && suite.commitment.None?
    {
      return Failure("Configuration conflict. Commitment policy requires only committing algorithm suites");
    }

    return Success(true);
  }

  /*
   * Validates that the given algorithm is allowed by the the given commitment policy
   * during decryption
   */
  method ValidateCommitmentPolicyOnDecrypt(
    algorithm: Option<Crypto.AlgorithmSuiteId>,
    commitmentPolicy: Crypto.CommitmentPolicy
  )
    returns (res: Result<bool, string>)

    // If an algorithm suite was not provided it cannot conflict with the
    // commitment policy
    ensures algorithm.None? ==> res.Success?

    // Commitment policy requires decrypting with commitment but the
    // algorithm does not provide it
    ensures
      (
        && commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        && algorithm.Some?
        && var suite := AlgorithmSuites.GetSuite(algorithm.value);
        && suite.commitment.None?
      )
    ==>
      res.Failure?
  {
    if algorithm.None? {
      return Success(true);
    }

    var suite := AlgorithmSuites.GetSuite(algorithm.value);

    if
      && commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
      && suite.commitment.None?
    {
      return Failure("Configuration conflict. Commitment policy requires only committing algorithm suites");
    }

    return Success(true);
  }
}