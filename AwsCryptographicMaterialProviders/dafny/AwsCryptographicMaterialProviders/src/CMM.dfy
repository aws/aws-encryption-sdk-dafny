// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Materials.dfy"

module {:options "/functionSyntax:4" } CMM {
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
      ensures output.Success?
      ==>
        && RequiredEncryptionContextKeys?(input.requiredEncryptionContextKeys, output.value.encryptionMaterials)

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
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //# The CMM MUST validate the [Encryption Context](structures.md#encryption-context)
      //# by comparing it to the customer supplied [Reproduced Encryption Context](structures.md#encryption-context)
      //# in [decrypt materials request](#decrypt-materials-request).
      //# For every key that exists in both [Reproduced Encryption Context](structures.md#encryption-context)
      //# and [Encryption Context](structures.md#encryption-context),
      //# the values MUST be equal or the operation MUST fail.
      ensures
        && (output.Success? ==> ReproducedEncryptionContext?(input))
        && (!ReproducedEncryptionContext?(input) ==> output.Failure?)
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //# - All key-value pairs that exist in [Reproduced Encryption Context](structures.md#encryption-context)
      //# but do not exist in encryption context on the [decrypt materials request](#decrypt-materials-request)
      //# SHOULD be appended to the decryption materials.
      ensures output.Success? ==> EncryptionContextComplete(input, output.value.decryptionMaterials)
  }

  predicate RequiredEncryptionContextKeys?(requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys>, encryptionMaterials: Types.EncryptionMaterials) {
    forall k <- requiredEncryptionContextKeys.UnwrapOr([])
      :: k in encryptionMaterials.requiredEncryptionContextKeys
  }

  predicate EncryptionContextComplete(input: Types.DecryptMaterialsInput, decryptionMaterials: Types.DecryptionMaterials) {
    var reproducedEncryptionContext := input.reproducedEncryptionContext.UnwrapOr(map[]);
    forall k <- reproducedEncryptionContext.Keys
      ::
        && k in decryptionMaterials.encryptionContext
        && decryptionMaterials.encryptionContext[k] == reproducedEncryptionContext[k]
  }

  predicate ReproducedEncryptionContext?(input: Types.DecryptMaterialsInput) {
    var reproducedEncryptionContext := input.reproducedEncryptionContext.UnwrapOr(map[]);
    forall k <- reproducedEncryptionContext.Keys
    | k in input.encryptionContext
    :: input.encryptionContext[k] == reproducedEncryptionContext[k]
  }
}
