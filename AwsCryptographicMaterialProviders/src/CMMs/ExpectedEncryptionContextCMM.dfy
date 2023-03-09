// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../CMM.dfy"
include "../Defaults.dfy"
include "../Commitment.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module ExpectedEncryptionContextCMM {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMM
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes
  import Seq

  class ExpectedEncryptionContextCMM
    extends CMM.VerifiableInterface
  {
    const underlyingCMM: Types.ICryptographicMaterialsManager
    const requiredEncryptionContextKeys: seq<UTF8.ValidUTF8Bytes>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && underlyingCMM.ValidState()
      && underlyingCMM.Modifies <= Modifies
      && History !in underlyingCMM.Modifies
    }

    constructor (
      c: Types.ICryptographicMaterialsManager,
      e: set<UTF8.ValidUTF8Bytes>
    )
      requires c.ValidState()
      // This is important.
      // A CMM that is a noop is not allowed.
      requires 0 < |e|
      ensures
        && |e| == |requiredEncryptionContextKeys|
        && forall k <- requiredEncryptionContextKeys :: k in e
      ensures
        && ValidState()
        && fresh(this)
        && fresh(History)
        && fresh(Modifies - underlyingCMM.Modifies)
      ensures Modifies == { History } + underlyingCMM.Modifies
    {
      var keySet := e;
      var keySeq := [];
      while keySet != {}
        invariant |keySeq| + |keySet| == |e|
        invariant forall k <- keySeq
        :: k in e
      {
        var key :| key in keySet;
        keySeq := keySeq + [key];
        keySet := keySet - {key};
      }

      underlyingCMM := c;
      requiredEncryptionContextKeys := keySeq;

      History := new Types.ICryptographicMaterialsManagerCallHistory();
      Modifies := { History } + c.Modifies;
    }

    predicate GetEncryptionMaterialsEnsuresPublicly(input: Types.GetEncryptionMaterialsInput, output: Result<Types.GetEncryptionMaterialsOutput, Types.Error>)
    {true}

    method GetEncryptionMaterials'(
      input: Types.GetEncryptionMaterialsInput
    )
      returns (output: Result<Types.GetEncryptionMaterialsOutput, Types.Error>)
      requires
      && ValidState() 
      modifies Modifies - {History}
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
      && ValidState()
      ensures GetEncryptionMaterialsEnsuresPublicly(input, output)
      ensures unchanged(History)

      // if the output materials are valid then they contain the required fields
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
      //= type=implication
      //# The encryption materials returned MUST include the following:

      // See EncryptionMaterialsHasPlaintextDataKey for details
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
      //= type=implication
      //# The CMM MUST ensure that the encryption materials returned are valid.
      //# - The encryption materials returned MUST follow the specification for [encryption-materials](structures.md#encryption-materials).
      //# - The value of the plaintext data key MUST be non-NULL.
      //# - The plaintext data key length MUST be equal to the [key derivation input length](algorithm-suites.md#key-derivation-input-length).
      //# - The encrypted data keys list MUST contain at least one encrypted data key.
      //# - If the algorithm suite contains a signing algorithm, the encryption materials returned MUST include the generated signing key.
      //# - For every key in [Required Encryption Context Keys](structures.md#required-encryption-context-keys)
      //#   there MUST be a matching key in the [Encryption Context](structures.md#encryption-context-1).
      ensures output.Success?
      ==>
        && Materials.EncryptionMaterialsHasPlaintextDataKey(output.value.encryptionMaterials)

      //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
      //= type=implication
      //# - The [Required Encryption Context Keys](structures.md#required-encryption-context-keys) MUST be
      //#   a super set of the Required Encryption Context Keys in the [encryption materials request](#encryption-materials-request).
      ensures output.Success?
      ==>
        && CMM.RequiredEncryptionContextKeys?(input.requiredEncryptionContextKeys, output.value.encryptionMaterials)

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#get-encryption-materials
      //= type=implication
      //# The encryption context on the [encryption materials request](./cmm-interface.md#encryption-materials-request)
      //# MUST contain a value for every key in the configured [required encryption context keys](#required-encryption-context-keys)
      //# or this request MUST fail.
      ensures !(forall k <- requiredEncryptionContextKeys :: k in input.encryptionContext)
      ==>
        output.Failure?

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#get-encryption-materials
      //= type=implication
      //# The Expected Encryption Context CMM MUST attempt to obtain [encryption materials](./structures.md#encryption-materials)
      //# by making a call to the [underlying CMM's](#underlying-cryptographic-materials-manager)
      //# [Get Encryption Materials](cmm-interface.md#get-encryption-materials).
      ensures
        && output.Success?
      ==>
        && |underlyingCMM.History.GetEncryptionMaterials| == |old(underlyingCMM.History.GetEncryptionMaterials)| + 1
        && Seq.Last(underlyingCMM.History.GetEncryptionMaterials).output.Success?
        && output == Seq.Last(underlyingCMM.History.GetEncryptionMaterials).output

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#get-encryption-materials
      //= type=implication
      //# All configured [required encryption context keys](#required-encryption-context-keys)
      //# MUST exist in the required encryption context keys
      //# of the [encryption materials request](./cmm-interface.md#encryption-materials-request)
      //# to the [underlying CMM's](#underlying-cryptographic-materials-manager).
      ensures
        && output.Success?
      ==>
        && Seq.Last(underlyingCMM.History.GetEncryptionMaterials).input.requiredEncryptionContextKeys.Some?
        && var keys := Seq.Last(underlyingCMM.History.GetEncryptionMaterials).input.requiredEncryptionContextKeys.value;
        && forall k <- requiredEncryptionContextKeys :: k in keys

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#get-encryption-materials
      //= type=implication
      //# The obtained [encryption materials](./structures.md#encryption-materials) MUST
      //# have all configured [required encryption context keys](#required-encryption-context-keys)
      //# in it's [required encryption context keys](./structures.md#required-encryption-context-keys).
      ensures
        && output.Success?
      ==>
        && forall k <- requiredEncryptionContextKeys
        :: k in output.value.encryptionMaterials.requiredEncryptionContextKeys
    {
      :- Need(forall k <- requiredEncryptionContextKeys :: k in input.encryptionContext,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Encryption context does not contain required keys.")
      );

      var result :- underlyingCMM.GetEncryptionMaterials(
        input.(
          requiredEncryptionContextKeys := 
          Some(input.requiredEncryptionContextKeys.UnwrapOr([]) + requiredEncryptionContextKeys))
      );

      :- Need(forall k <- requiredEncryptionContextKeys :: k in result.encryptionMaterials.requiredEncryptionContextKeys,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Expected encryption context keys do not exist in keys to only authenticate.")
      );

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.EncryptionMaterialsHasPlaintextDataKey(result.encryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Could not retrieve materials required for encryption"));
      :- Need(
        CMM.RequiredEncryptionContextKeys?(input.requiredEncryptionContextKeys, result.encryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring returned an invalid response"));

      output := Success(result);
    }

    predicate DecryptMaterialsEnsuresPublicly(input: Types.DecryptMaterialsInput, output: Result<Types.DecryptMaterialsOutput, Types.Error>)
    {true}

    method DecryptMaterials'(
      input: Types.DecryptMaterialsInput
    )
      returns (output: Result<Types.DecryptMaterialsOutput, Types.Error>)
      requires
      && ValidState() 
      modifies Modifies - {History}
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
      && ValidState()
      ensures DecryptMaterialsEnsuresPublicly(input, output)
      ensures unchanged(History)

      ensures output.Success?
      ==>
        && Materials.DecryptionMaterialsWithPlaintextDataKey(output.value.decryptionMaterials)

      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# The CMM MUST validate the [Encryption Context](structures.md#encryption-context)
      //# by comparing it to the customer supplied [Reproduced Encryption Context](structures.md#encryption-context)
      //# in [decrypt materials request](#decrypt-materials-request).
      //# For every key that exists in both [Reproduced Encryption Context](structures.md#encryption-context)
      //# and [Encryption Context](structures.md#encryption-context),
      //# the values MUST be equal or the operation MUST fail.
      ensures
        && (output.Success? ==> CMM.ReproducedEncryptionContext?(input))
        && (!CMM.ReproducedEncryptionContext?(input) ==> output.Failure?)
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# - All key-value pairs that exist in [Reproduced Encryption Context](structures.md#encryption-context)
      //# but do not exist in encryption context on the [decrypt materials request](#decrypt-materials-request)
      //# SHOULD be appended to the decryption materials.
      ensures output.Success? ==> CMM.EncryptionContextComplete(input, output.value.decryptionMaterials)

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#decrypt-materials
      //= type=implication
      //# The reproduced encryption context on the [decrypt materials request](./cmm-interface.md#decrypt-materials-request)
      //# MUST contain a value for every key in the configured [required encryption context keys](#required-encryption-context-keys)
      //# or this request MUST fail.
      ensures
        && (output.Success?
      ==>
        && input.reproducedEncryptionContext.Some?
        && forall k <- requiredEncryptionContextKeys :: k in input.reproducedEncryptionContext.value)
      ensures input.reproducedEncryptionContext.None? ==> output.Failure?
      ensures
        && input.reproducedEncryptionContext.Some?
        && !(forall k <- requiredEncryptionContextKeys :: k in input.reproducedEncryptionContext.value)
      ==> output.Failure?

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#decrypt-materials
      //= type=implication
      //# The Expected Encryption Context
      //# CMM MUST attempt to obtain [decryption materials](./structures.md#decryption-materials)
      //# by making a call to the [underlying CMM's](#underlying-cryptographic-materials-manager)
      //# [decrypt materials](cmm-interface.md#decrypt-materials) interface
      //# with the unchanged [decrypt materials request](./cmm-interface.md#decrypt-materials-request).
      ensures output.Success?
      ==>
        && |underlyingCMM.History.DecryptMaterials| == |old(underlyingCMM.History.DecryptMaterials)| + 1
        && Seq.Last(underlyingCMM.History.DecryptMaterials).output == output
        && Seq.Last(underlyingCMM.History.DecryptMaterials).input == input

      //= aws-encryption-sdk-specification/framework/required-encryption-context-cmm.md#decrypt-materials
      //= type=implication
      //# The obtained [decryption materials](./structures.md#decryption-materials) MUST
      //# have all configured [required encryption context keys](#required-encryption-context-keys)
      //# in it's [encryption context](./structures.md#encryption-context-2).
      ensures
        && |underlyingCMM.History.DecryptMaterials| == |old(underlyingCMM.History.DecryptMaterials)| + 1
        && Seq.Last(underlyingCMM.History.DecryptMaterials).output.Success?
        && !(forall k <- requiredEncryptionContextKeys
          :: k in Seq.Last(underlyingCMM.History.DecryptMaterials).output.value.decryptionMaterials.encryptionContext)
      ==> output.Failure?

    {

      :- Need(input.reproducedEncryptionContext.Some?,
        Types.AwsCryptographicMaterialProvidersException(
          message := "No reproduced encryption context on decrypt.")
      );

      :- Need(CMM.ReproducedEncryptionContext?(input),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Encryption context does not match reproduced encryption context.")
      );

      :- Need(forall k <- requiredEncryptionContextKeys :: k in input.reproducedEncryptionContext.value,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Reproduced encryption context missing required keys.")
      );

      var result :- underlyingCMM.DecryptMaterials(input);

      :- Need(forall k <- requiredEncryptionContextKeys :: k in result.decryptionMaterials.encryptionContext,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Final encryption context missing required keys.")
      );

      :- Need(CMM.EncryptionContextComplete(input, result.decryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Reproduced encryption context missing from encryption context.")
      );

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.DecryptionMaterialsWithPlaintextDataKey(result.decryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring.OnDecrypt failed to decrypt the plaintext data key."));

      return Success(result);
    }
  }
}
