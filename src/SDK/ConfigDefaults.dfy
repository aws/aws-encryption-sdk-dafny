// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

/*
 * This module contains methods for translating the ConfigurationDefaults
 * parameter (that is passed into client creation) into the individual
 * default configurations it controls (e.g. commitment policy)
 */
module {:extern "ConfigDefaults"} ConfigDefaults {

  import Aws
  import opened UInt = StandardLibrary.UInt

  function method GetDefaultCommitmentPolicy(configDefaults : Aws.Esdk.ConfigurationDefaults):
    (res: Aws.Crypto.CommitmentPolicy)
    
    //= compliance/client-apis/client.txt#2.4
    //= type=implication
    //# If no commitment policy (Section 2.4.1) is provided the default MUST
    //# be REQUIRE_ENCRYPT_REQUIRE_DECRYPT (../framework/algorithm-
    //# suites.md#require_encrypt_require_decrypt).
    ensures
      configDefaults == Aws.Esdk.V1 ==> res == Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT

  {
      Aws.Crypto.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
    }
}
