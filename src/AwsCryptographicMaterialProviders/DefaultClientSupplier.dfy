// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../Generated/KeyManagementService.dfy"
include "../Generated/AwsCryptographicMaterialProviders.dfy"

module
  {:extern "DefaultClientSupplier"}
  MaterialProviders.DefaultClientSupplier
 {
  import KMS = Com.Amazonaws.Kms
  import Aws.Crypto
  import opened Wrappers  
    
  class DefaultClientSupplier
    extends Crypto.IClientSupplier
  {

    constructor(){}

    method {:extern "DefaultClientSupplier.DefaultClientSupplier", "GetClient"} GetClient(input: Crypto.GetClientInput)
      returns (res: Result<KMS.IKeyManagementServiceClient, Crypto.AwsCryptographicMaterialProvidersClientException>) 
    
  }
}
