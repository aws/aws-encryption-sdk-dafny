// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../../src/AwsCryptographicMaterialProviders/Client.dfy"
include "../../../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../../src/StandardLibrary/StandardLibrary.dfy"
include "../../../Util/TestUtils.dfy"
include "../TestMultiKeyring.dfy"

module TestMrkAwareDiscoveryMultiKeyring {    
  import Aws.Crypto
  import MaterialProviders.Client
  import TestMultiKeyring  
  import opened TestUtils    
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers

  method {:test} HappyPath()
  {
    // Create material provider client
    var materialsClient := new Client.AwsCryptographicMaterialProvidersClient();

    var mrkAwareDiscoveryMultiKeyringResult := materialsClient.CreateMrkAwareDiscoveryMultiKeyring(
      Crypto.CreateMrkAwareDiscoveryMultiKeyringInput(
        regions := ["us-west-2", "us-east-1"],
        discoveryFilter := Option.None,
        grantTokens := Option.None,
        clientSupplier := null
      )
    );
    expect mrkAwareDiscoveryMultiKeyringResult.Success?;
    var mrkAwareDiscoveryMultiKeyring := mrkAwareDiscoveryMultiKeyringResult.Extract();

    // var cmmResult := materialsClient.CreateDefaultCryptographicMaterialsManager(
    //   Crypto.CreateDefaultCryptographicMaterialsManagerInput(
    //     keyring := mrkAwareDiscoveryMultiKeyring
    //   )
    // );
    // expect cmmResult.Success?;
    // var cmm := cmmResult.Extract();

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var encryptionMaterials := TestMultiKeyring.getInputEncryptionMaterials(encryptionContext);
    var decryptionMaterials := TestMultiKeyring.getInputDecryptionMaterials(encryptionContext);

    var result := mrkAwareDiscoveryMultiKeyring.OnEncrypt(
      Crypto.OnEncryptInput(materials:=encryptionMaterials)
    );
    if result.Failure? {
      print result;
    }
    expect result.Success?;
  }

}  
