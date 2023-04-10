// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "TestUtils.dfy"

module TestDefaultClientProvider {
  import Types = AwsCryptographyMaterialProvidersTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import MaterialProviders
  import opened TestUtils
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  method {:test} GetUsWestTwo() {
    // Create material provider client
    var mpl :- expect MaterialProviders.MaterialProviders();

    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());

    var client :- expect clientSupplier.GetClient(
      Types.GetClientInput(
        region := "us-west-2"
      )
    );

    var kmsRequest := ComAmazonawsKmsTypes.GenerateDataKeyRequest(
      KeyId := TestUtils.SHARED_TEST_KEY_ARN,
      EncryptionContext := Option.None,
      GrantTokens := Option.None,
      NumberOfBytes := Option.Some(24 as int32),
      KeySpec := Option.None
    );

    var kmsReply :- expect client.GenerateDataKey(kmsRequest);
  }
}
