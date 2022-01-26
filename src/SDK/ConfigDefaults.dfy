
include "../Generated/AwsEncryptionSdk.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

/*
 * This module contains methods for translating the ConfigurationDefaults
 * parameter (that is passed into client creation) into the individual
 * default configurations it controls (e.g. commitment policy)
 */
module {:extern "ConfigDefaults"} ConfigDefaults {

  import Aws

  method GetDefaultCommitmentPolicy(configDefaults : Aws.Esdk.ConfigurationDefaults)
    returns (res: Aws.Crypto.CommitmentPolicy)

    ensures
      //configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
      configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
    {
      // TODO: actual matching on version
      // For now defaulting to the FORBID_ENCRYPT version because don't yet support commiting alg suites
      return Aws.Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT;
    }
}
