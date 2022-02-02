// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Generated/AwsCryptographicMaterialProviders.dfy"


module {:extern "Defaults"} Defaults {
  import Aws.Crypto

  /* Returns the default algorithm suite for the given commitment policy */
  // TODO: move to default commitment algorithms once supported by the rest of the code
  function method GetAlgorithmSuiteForCommitmentPolicy(commitmentPolicy: Crypto.CommitmentPolicy):
    (res: Crypto.AlgorithmSuiteId)

    ensures
      commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT
      ==>
      res == Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384

    ensures
      || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
      || commitmentPolicy == Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
      ==>
      res == Crypto.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
  {
    if commitmentPolicy == Crypto.FORBID_ENCRYPT_ALLOW_DECRYPT then
      Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 else
      Crypto.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
  }
}
