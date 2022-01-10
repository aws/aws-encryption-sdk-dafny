// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Add extern reference for a native AWS KMS service client
module {:extern "Amazon.KeyManagementService"} AmazonKeyManagementService {
  // IAmazonKeyManagementService is an interface in target languages, but is listed as a class instead of a trait
  // because the Dafny transpiler cannot currently allow an extern interface to be used as a Dafny trait.
  // It only allows a Dafny trait to be used as an extern interface, not the other way around.
  // By making this a trait, compilation fails because this causes a conflict with the actual Amazon.KeyManagementService.IAmazonKeyManagementService
  // TODO: https://github.com/awslabs/aws-encryption-sdk-dafny/issues/284
  class {:extern "IAmazonKeyManagementService"} IAmazonKeyManagementService {}

  predicate method {:extern "RegionMatch"} RegionMatch(
    client: IAmazonKeyManagementService,
    region: string
  )
}
