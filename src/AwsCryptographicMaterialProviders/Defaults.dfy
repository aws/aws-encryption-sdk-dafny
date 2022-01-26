
include "../Generated/AwsCryptographicMaterialProviders.dfy"


module {:extern "Defaults"} Defaults {
  import Aws.Crypto

  /* Returns the default algorithm suite for the given commitment policy */
  // TODO: move to default commitment algorithms once supported by the rest of the code
  method GetAlgorithmSuiteForCommitmentPolicy(commitmentPolicy: Crypto.CommitmentPolicy)
    returns (res: Crypto.AlgorithmSuiteId)
    ensures
      commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
      ==>
      res == Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
    ensures
      || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
      || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
      ==>
      //res == Crypto.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
      res == Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
  {
    if commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT {
      return Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
    } else if commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT ||
              commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT {
      return Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      //return Crypto.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384;
    }
  }
}