// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/AwsCryptographicMaterialProviders/Client.dfy"
include "../../src/Generated/AwsCryptographicMaterialProviders.dfy"
include "../../src/Generated/KeyManagementService.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../Util/TestUtils.dfy"

module TestDefaultClientProvider {
  import Aws.Crypto
  import KMS = Com.Amazonaws.Kms
  import MaterialProviders.Client
  import opened TestUtils
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  
  method {:test} GetUsWestTwo() {
    // Create material provider client
    var materialsClient := new Client.AwsCryptographicMaterialProvidersClient();

    var clientSupplier: Crypto.IClientSupplier;
    var clientSupplierOutput := materialsClient.CreateDefaultClientSupplier(
      Crypto.CreateDefaultClientSupplierInput()
    );
    clientSupplier := clientSupplierOutput.clientSupplier;
    var clientRes := clientSupplier.GetClient(
      Crypto.GetClientInput(
        "us-west-2"
      )
    );
    var client : KMS.IKeyManagementServiceClient?;
    match clientRes {
      case Failure(error) => {
        print error.GetMessage();
      }   
      case Success(value) => client := clientRes.value;
    }

    expect clientRes.Success?;
    assert clientRes.Success?;
    assert client != null;
    
    var kmsRequest := KMS.GenerateDataKeyRequest(
      KeyId := TestUtils.SHARED_TEST_KEY_ARN,
      EncryptionContext := Option.None,
      GrantTokens := Option.None,
      NumberOfBytes := Option.Some(24 as int32),
      KeySpec := Option.None
    );

    var kmsReply := client.GenerateDataKey(kmsRequest);
    match kmsReply {
      case Failure(error) => {
        print KMS.CastKeyManagementServiceErrorToString(error);
      }
      case Success(value) => return;
    }
  }

}
