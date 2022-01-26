
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
      configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
    {
      // TODO: actual matching on version
      return Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
}
