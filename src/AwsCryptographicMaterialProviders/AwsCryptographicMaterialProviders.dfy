// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"
include "../Generated/AwsEncryptionSdk.dfy"
include "../Util/UTF8.dfy"
include "AlgorithmSuites.dfy"

module {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient2"} AwsCryptographicMaterialProviders2 {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened AlgorithmSuites
  import UTF8
  import Aws.Crypto
  import Aws.Esdk

}
