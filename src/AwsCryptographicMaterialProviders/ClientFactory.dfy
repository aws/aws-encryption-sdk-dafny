// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "Client.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersFactory"} MaterialProviders.ClientFactory {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import Aws.Crypto
  import Client

  class AwsCryptographicMaterialProvidersFactory extends Crypto.IAwsCryptographicMaterialProvidersFactory {

    constructor() {}

    method CreateDefaultAwsCryptographicMaterialProviders()
          returns (res: Result<Crypto.IAwsCryptographicMaterialProviders, Crypto.IAwsCryptographicMaterialProvidersException>)
    {
        var client := new Client.AwsCryptographicMaterialProviders();
        return Success(client);
    }
  }
}
