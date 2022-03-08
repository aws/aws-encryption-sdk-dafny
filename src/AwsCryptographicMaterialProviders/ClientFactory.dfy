// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "Client.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientFactory"} MaterialProviders.ClientFactory {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Crypto
  import Client

  class AwsCryptographicMaterialProvidersClientFactory extends Crypto.IAwsCryptographicMaterialProvidersClientFactory {

    constructor() {}

    method MakeAwsCryptographicMaterialProvidersClient(input: Crypto.AwsCryptographicMaterialProvidersClientConfig)
          returns (res: Result<Crypto.IAwsCryptographicMaterialProvidersClient, Crypto.IAwsCryptographicMaterialProvidersClientException>)
    {
        var client := new Client.AwsCryptographicMaterialProvidersClient(input);
        return Success(client);
    }
  }
}
