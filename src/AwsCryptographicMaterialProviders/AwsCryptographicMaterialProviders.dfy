// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Util/UTF8.dfy"
include "AlgorithmSuites.dfy"
include "Materials.dfy"
include "Keyring.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient2"} AwsCryptographicMaterialProviders2 {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened AlgorithmSuites
  import UTF8
  import Aws.Crypto
  import A = AlgorithmSuites
  import M = Materials
  import K = Keyring

}
