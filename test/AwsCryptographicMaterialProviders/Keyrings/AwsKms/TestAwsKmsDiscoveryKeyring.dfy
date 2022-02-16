// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/AwsCryptographicMaterialProviders/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../../src/StandardLibrary/Actions.dfy"
include "../../../../src/Util/UTF8.dfy"
include "../../../Util/TestUtils.dfy"


module TestAwsKmsDiscoveryKeyring {
  import Aws.Crypto
  import MaterialProviders.AwsKmsDiscoveryKeyring
  import opened TestUtils    
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
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
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(
      Option.Some(discoveryFilter)
    );
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

  //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
  //= type=test
  //# The set of encrypted data keys MUST first be filtered to match this
  //# keyring's configuration.
  method {:test} TestAwsKmsEncryptedDataKeyFilterMatchesKeyringsConfiguration()
  {
    var matchingEdk := GenerateMockEncryptedDataKey("aws-kms", SHARED_TEST_KEY_ARN);
    var mismatchEdkPartition := GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws-cn:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
    var mismatchEdkAccount := GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws:kms:us-west-2:827585335069:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
    var mismatchEdkProviderId := GenerateMockEncryptedDataKey(
      "aws",
      SHARED_TEST_KEY_ARN
    );
    var discoveryFilter := GetDiscoveryFilter();
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(
      Option.Some(discoveryFilter)
    );
    var filterResult := Actions.FilterWithResult(
      edkFilter,
      [matchingEdk, mismatchEdkPartition, mismatchEdkAccount, mismatchEdkProviderId]
    );
    expect filterResult.Success?;
    expect |filterResult.value| == 1;
    expect filterResult.value[0] == matchingEdk;
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
    edk := GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws:kms:us-west-2:658956600833:alias/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
  }

  method NoOp()
  {
    return;
  }
  
}
