// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypesWrapped.dfy"

module
  {:extern "Dafny.Aws.Cryptography.MaterialProviders.Wrapped" }
  WrappedMaterialProviders refines WrappedAbstractAwsCryptographyMaterialProvidersService
{
  import WrappedService = MaterialProviders

  function method WrappedDefaultMaterialProvidersConfig(): MaterialProvidersConfig
  {
    MaterialProvidersConfig
  }

}
