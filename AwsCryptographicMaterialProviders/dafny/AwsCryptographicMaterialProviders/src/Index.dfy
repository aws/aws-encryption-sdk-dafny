// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AwsCryptographyMaterialProvidersOperations.dfy"

module
  {:extern "Dafny.Aws.Cryptography.MaterialProviders" }
  MaterialProviders refines AbstractAwsCryptographyMaterialProvidersService
{

  import Operations = AwsCryptographyMaterialProvidersOperations
  import Aws.Cryptography.Primitives

  function method DefaultMaterialProvidersConfig(): MaterialProvidersConfig
  {
    MaterialProvidersConfig
  }

  method MaterialProviders(config: MaterialProvidersConfig)
    returns (res: Result<MaterialProvidersClient, Error>)
  {
    var maybeCrypto := Primitives.AtomicPrimitives();
    var crypto :- maybeCrypto
      .MapFailure(e => AwsCryptographyPrimitives(e));
    var client := new MaterialProvidersClient(Operations.Config( crypto := crypto ));
    return Success(client);
  }

  class MaterialProvidersClient... {

    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IAwsCryptographicMaterialProvidersClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

  }

}
