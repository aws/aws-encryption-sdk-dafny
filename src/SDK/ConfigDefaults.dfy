
include "../Generated/AwsEncryptionSdk.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "ConfigDefaults"} ConfigDefaults {

  import Aws

  method GetDefaultCommitmentPolicy(configDefaults : Aws.Esdk.ConfigurationDefaults)
    returns (res: Aws.Crypto.CommitmentPolicy) {

      // TODO: actual matching on version
      return Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT;
    }
}
