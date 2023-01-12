// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/Index.dfy"
include "../../../src/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../TestUtils.dfy"
include "../../../../ComAmazonawsKms/src/Index.dfy"

module TestAwsKmsRsaKeyring {
  import opened Wrappers
   import opened UInt = StandardLibrary.UInt
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes
  import AwsKmsRsaKeyring
  import TestUtils
  import ComAmazonawsKmsTypes

  // Smoke tests for valid configurations
  // TODO These should eventually be covered by formal verification

  method {:test} TestValidEncryptOnlyConfiguration() {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var publicKey: seq<uint8> := []; // TODO for now empty bytestring is accepted

    var result :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(
        publicKey := Some(publicKey),
        kmsKeyId := TestUtils.SHARED_TEST_KEY_ARN,
        encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1,
        kmsClient := None(),
        grantTokens := None()
    ));
  }

  method {:test} TestValidDecryptOnlyConfiguration() {
    var mpl :- expect MaterialProviders.MaterialProviders();

    // TODO awkward way to initialize a KMS client
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region:="us-west-2"));

    var result :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(
        publicKey := None(),
        kmsKeyId := TestUtils.SHARED_TEST_KEY_ARN,
        encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1,
        kmsClient := Some(kmsClient),
        grantTokens := None()
    ));
  }

  method {:test} TestValidEncryptDecryptConfiguration() {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var publicKey: seq<uint8> := []; // TODO for now empty bytestring is accepted

    // TODO awkward way to initialize a KMS client
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region:="us-west-2"));

    var result :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(
        publicKey := Some(publicKey),
        kmsKeyId := TestUtils.SHARED_TEST_KEY_ARN,
        encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1,
        kmsClient := Some(kmsClient),
        grantTokens := None()
    ));
  }
}
