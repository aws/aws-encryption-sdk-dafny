// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/AwsCryptographicMaterialProviders/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../../../src/AwsCryptographicMaterialProviders/Keyrings/AwsKms/Constants.dfy"
// include "../../../../src/AwsCryptographicMaterialProviders/Client.dfy"
include "../../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../../src/StandardLibrary/Actions.dfy"
include "../../../../src/Util/UTF8.dfy"
include "../../../Util/TestUtils.dfy"


module TestAwsKmsDiscoveryKeyring {
  import Aws.Crypto
    // import MaterialProviders.Client
  import MaterialProviders.AwsKmsDiscoveryKeyring
  import opened TestUtils    
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import opened Constants
  import opened Actions
  import UTF8  

  //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
  //= type=test
  //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
  //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
  //# OnDecrypt MUST fail.
  method {:test} TestAwsKmsEncryptedDataKeyFilterFailsNonKeyResource()
  {
    var discoveryFilter := GetDiscoveryFilter();
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(Option.Some(discoveryFilter));
    var badEdk := GetNonKeyEncryptedDataKey();
    var filterResult := Actions.FilterWithResult(edkFilter, [badEdk]);
    match filterResult {
      case Failure(errorString) => {
        expect errorString == "Only AWS KMS Keys supported";
      }
      case Success => NoOp();
    }
    expect filterResult.Failure?;
  }

  method GetDiscoveryFilter() returns (discoveryFilter: Crypto.DiscoveryFilter)
  {
    return Crypto.DiscoveryFilter(
      ACCOUNT_IDS,
      PARTITION
    );
  }

  method GetNonKeyEncryptedDataKey() returns (edk: Crypto.EncryptedDataKey)
  {
    var keyProviderInfo :- expect UTF8.Encode(
      "arn:aws:kms:us-west-2:658956600833:alias/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
    var fakeCiphertext :- expect UTF8.Encode(
      "fakeCiphertext"
    );
    return Crypto.EncryptedDataKey(
      keyProviderId := PROVIDER_ID,
      keyProviderInfo := keyProviderInfo,
      ciphertext := fakeCiphertext
    );
  }

  method NoOp()
  {
    return;
  }
  
}
