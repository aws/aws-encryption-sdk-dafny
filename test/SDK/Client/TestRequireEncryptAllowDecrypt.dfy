// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../src/Generated/AwsEncryptionSdk.dfy"
include "../../../src/SDK/AwsEncryptionSdk.dfy"
include "../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../src/StandardLibrary/UInt.dfy"
include "../../../src/Util/UTF8.dfy"
include "../../Util/TestUtils.dfy"

module TestRequireEncryptAllowDecrypt {
  import Aws.Crypto
  import Aws.Esdk
  import AwsEncryptionSdk
  import MaterialProviders.Client
  import TestUtils
  import UTF8
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  //   When the commitment policy "REQUIRE_ENCRYPT_ALLOW_DECRYPT" is
  // configured:

  //= compliance/client-apis/client.txt#2.4.2.2
  //= type=TODO
  //# *  "05 78" MUST be the default algorithm suite

  //= compliance/client-apis/client.txt#2.4.2.2
  //= type=TODO
  //# *  encrypt (encrypt.md) MUST only support algorithm suites that have
  //# a Key Commitment (../framework/algorithm-suites.md#algorithm-
  //# suites-encryption-key-derivation-settings) value of True

  //= compliance/client-apis/client.txt#2.4.2.2
  //= type=TODO
  //# *  decrypt (decrypt.md) MUST support all algorithm suites

}
