// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module DefaultClientSupplier {
  import ComAmazonawsKmsTypes
  import Com.Amazonaws.Kms
  import opened AwsCryptographyMaterialProvidersTypes

  import opened Wrappers  

  class DefaultClientSupplier
    extends IClientSupplier
  {

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }
    constructor()
    ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      History := new IClientSupplierCallHistory();
      Modifies := { History };
    }

    predicate GetClientEnsuresPublicly(input: GetClientInput, output: Result<ComAmazonawsKmsTypes.IKMSClient, Error>)
    {true}
    
    method GetClient'(input: GetClientInput)
      returns (output: Result<ComAmazonawsKmsTypes.IKMSClient, Error>)
      requires
      && ValidState() 
      modifies Modifies - {History}
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
      && ValidState()
      && ( output.Success? ==> 
        && output.value.ValidState()
        && output.value.Modifies !! Modifies
        && fresh(output.value)
        && fresh ( output.value.Modifies  )
      )
      ensures GetClientEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      var maybeClient := Kms.KMSClientForRegion(input.region);
      return maybeClient.MapFailure(e => ComAmazonawsKms(e));
    }

  }
}
