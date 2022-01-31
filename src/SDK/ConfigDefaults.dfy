
include "../Generated/AwsEncryptionSdk.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

/*
 * This module contains methods for translating the ConfigurationDefaults
 * parameter (that is passed into client creation) into the individual
 * default configurations it controls (e.g. commitment policy)
 */
module {:extern "ConfigDefaults"} ConfigDefaults {

  import Aws

  function method GetDefaultCommitmentPolicy(configDefaults : Aws.Esdk.ConfigurationDefaults):
    (res: Aws.Crypto.CommitmentPolicy)

    ensures
      configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
    {
      // TODO: actual matching on version
      // TODO: we don't yet support commitment
      Aws.Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
    }
}
