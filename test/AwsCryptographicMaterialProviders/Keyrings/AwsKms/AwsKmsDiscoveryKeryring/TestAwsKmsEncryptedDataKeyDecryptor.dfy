// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../../src/AwsCryptographicMaterialProviders/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../../../src/StandardLibrary/Actions.dfy"
include "../../../../../src/Util/UTF8.dfy"
include "../../../../Util/TestUtils.dfy"


module AwsKmsEncryptedDataKeyFilter {
  import Aws.Crypto
  import MaterialProviders.AwsKmsDiscoveryKeyring
  import opened TestUtils    
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import opened Actions
  import UTF8

  //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
  //= type=test
  //# For each encrypted data key in the filtered set, one at a time, the
  //# OnDecrypt MUST attempt to decrypt the data key.
  method {:test} Test()
  {
  }

}
