// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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
      configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
    {
      // TODO: actual matching on version
      Aws.Crypto.REQUIRE_ENCRYPT_ALLOW_DECRYPT
    }
}
