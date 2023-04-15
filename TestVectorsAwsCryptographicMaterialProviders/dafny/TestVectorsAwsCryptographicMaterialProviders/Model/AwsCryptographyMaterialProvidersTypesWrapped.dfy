// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../../StandardLibrary/src/Index.dfy"
// BEGIN MANUAL EDIT
 include "../../../../AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/Index.dfy"
// END MANUAL EDIT
 abstract module WrappedAbstractAwsCryptographyMaterialProvidersService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyMaterialProvidersTypes
 import WrappedService : AbstractAwsCryptographyMaterialProvidersService
 function method WrappedDefaultMaterialProvidersConfig(): MaterialProvidersConfig
 method {:extern} WrappedMaterialProviders(config: MaterialProvidersConfig := WrappedDefaultMaterialProvidersConfig())
 returns (res: Result<IAwsCryptographicMaterialProvidersClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
