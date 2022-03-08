// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "Client.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClientFactoryClient"} MaterialProviders.ClientFactory {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Crypto
  import Client

  class AwsCryptographicMaterialProvidersClientFactoryClient extends Crypto.IAwsCryptographicMaterialProvidersClientFactoryClient {

    constructor() {}

    method MakeAwsCryptographicMaterialProvidersClient(input: Crypto.AwsCryptographicMaterialProvidersClientConfig)
          returns (res: Result<Crypto.IAwsCryptographicMaterialProvidersClient, Crypto.IAwsCryptographicMaterialProvidersClientFactoryException>)
    {
        var client := new Client.AwsCryptographicMaterialProvidersClient(input);
        return Success(client);
    }
  }
}
