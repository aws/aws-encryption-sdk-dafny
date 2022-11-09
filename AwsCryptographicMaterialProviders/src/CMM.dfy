// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Materials.dfy"

module CMM {
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import Materials

  trait {:termination false} VerifiableInterface
    extends Types.ICryptographicMaterialsManager
  {
    method GetEncryptionMaterials'(input: Types.GetEncryptionMaterialsInput)
      returns (output: Result<Types.GetEncryptionMaterialsOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures ValidState()
      ensures GetEncryptionMaterialsEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures output.Success?
      ==>
        && Materials.EncryptionMaterialsHasPlaintextDataKey(output.value.encryptionMaterials)

    method DecryptMaterials'(input: Types.DecryptMaterialsInput)
    returns (output: Result<Types.DecryptMaterialsOutput, Types.Error>)
    requires ValidState()
    modifies Modifies - {History}
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases Modifies - {History}
    ensures ValidState()
    ensures DecryptMaterialsEnsuresPublicly(input, output)
    ensures unchanged(History)
      ensures output.Success?
      ==>
        && Materials.DecryptionMaterialsWithPlaintextDataKey(output.value.decryptionMaterials)
  }
}
