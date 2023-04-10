// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/Index.dfy"
include "../../../../src/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../../TestUtils.dfy"

module TestAwsKmsEncryptedDataKeyFilter {
  import opened Wrappers
  import TestUtils
  import UTF8
  import Aws.Cryptography.Primitives
  import AwsCryptographyPrimitivesTypes
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes
  import AwsKmsDiscoveryKeyring
  import Actions
  
  //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
  //= type=test
  //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
  //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
  //# OnDecrypt MUST fail.
  method {:test} TestFailsNonKeyResource()
  {
    var discoveryFilter := GetDiscoveryFilter();
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(
      Option.Some(discoveryFilter)
    );
    var badEdk := GetNonKeyEncryptedDataKey();
    var filterResult := Actions.FilterWithResult(edkFilter, [badEdk]);
    expect filterResult.Failure?;
    var test: Types.Error := filterResult.error;
    expect test.AwsCryptographicMaterialProvidersException?;
    expect test.message == "Only AWS KMS Keys supported";
  }

  //= compliance/framework/aws-kms/aws-kms-discovery-keyring.txt#2.8
  //= type=test
  //# The set of encrypted data keys MUST first be filtered to match this
  //# keyring's configuration.
  method {:test} TestMatchesKeyringsConfiguration()
  {
    var matchingEdk := TestUtils.GenerateMockEncryptedDataKey("aws-kms", TestUtils.SHARED_TEST_KEY_ARN);
    var mismatchEdkPartition := TestUtils.GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws-cn:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
    var mismatchEdkAccount := TestUtils.GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws:kms:us-west-2:827585335069:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
    var mismatchEdkProviderId := TestUtils.GenerateMockEncryptedDataKey(
      "aws",
      TestUtils.SHARED_TEST_KEY_ARN
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

  method GetDiscoveryFilter() returns (discoveryFilter: Types.DiscoveryFilter)
  {
    return Types.DiscoveryFilter(
      accountIds := TestUtils.ACCOUNT_IDS,
      partition := TestUtils.PARTITION
    );
  }

  method GetNonKeyEncryptedDataKey() returns (edk: Types.EncryptedDataKey)
  {
    edk := TestUtils.GenerateMockEncryptedDataKey(
      "aws-kms",
      "arn:aws:kms:us-west-2:658956600833:alias/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
    );
  }
}
