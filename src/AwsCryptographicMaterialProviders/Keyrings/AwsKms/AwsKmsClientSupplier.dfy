// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../Generated/KeyManagementService.dfy"
include "../../../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "Aws.Crypto.ClientSupplierBase"} ClientSupplier {
  import KMS = Com.Amazonaws.Kms
  import Aws.Crypto
    
  class BaseClientSupplier extends Crypto.IClientSupplier {

    constructor(){}

    method {:extern "Aws.Crypto.ClientSupplierBase", "GetClient"} GetClient(input: Crypto.GetClientInput) returns (res: KMS.IKeyManagementServiceClient?) 
    
  }
}
