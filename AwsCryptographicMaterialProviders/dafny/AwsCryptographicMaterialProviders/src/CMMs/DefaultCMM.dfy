// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../CMM.dfy"
include "../Defaults.dfy"
include "../Commitment.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module DefaultCMM {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuites
  import Materials
  import CMM
  import Signature
  import Base64
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import Aws.Cryptography.Primitives
  import Defaults
  import Commitment
  import Seq

  class DefaultCMM
    extends CMM.VerifiableInterface
  {
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && keyring.ValidState()
      && cryptoPrimitives.ValidState()
      && keyring.Modifies <= Modifies
      && cryptoPrimitives.Modifies <= Modifies
      && History !in keyring.Modifies
      && History !in cryptoPrimitives.Modifies
    }

    const keyring: Types.IKeyring

    constructor OfKeyring(
      //= aws-encryption-sdk-specification/framework/default-cmm.md#initialization
      //= type=implication
      //# On default CMM initialization,
      //# the caller MUST provide the following value:
      //# - [Keyring](#keyring)
      k: Types.IKeyring,
      c: Primitives.AtomicPrimitivesClient
    )
      requires k.ValidState() && c.ValidState()
      ensures keyring == k && cryptoPrimitives == c
      ensures
        && ValidState()
        && fresh(this)
        && fresh(History)
        && fresh(Modifies - cryptoPrimitives.Modifies - keyring.Modifies)
      ensures Modifies == { History } + keyring.Modifies + cryptoPrimitives.Modifies
    {
      keyring := k;
      cryptoPrimitives := c;

      History := new Types.ICryptographicMaterialsManagerCallHistory();
      Modifies := { History } + c.Modifies + k.Modifies;
    }

    predicate GetEncryptionMaterialsEnsuresPublicly(input: Types.GetEncryptionMaterialsInput, output: Result<Types.GetEncryptionMaterialsOutput, Types.Error>)
    {true}

    // The following are requirements for the CMM interface.
    // However they are requirments of intent
    // rather than something that can be verified programaticly.
    // The configured keyring could violate these properties.
    // This is why these are listed as exception and not implications.
    // 
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
    //= type=exception
    //# When the CMM gets an [encryption materials request](#encryption-materials-request),
    //# it MUST return [encryption materials](structures.md#encryption-materials) appropriate for the request.
    //
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
    //= type=exception
    //# - Every encrypted data key in this list MUST correspond to the above plaintext data key.

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

      //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
      //= type=implication
      //# If the algorithm suite contains a [signing algorithm](algorithm-suites.md#signature-algorithm):
      //# 
      //# - The CMM MUST include a [signing key](structures.md#signing-key).
      //# - The CMM SHOULD also add a key-value pair using the reserved key `aws-crypto-public-key` to the encryption context.
      //#   If it does, the mapped value SHOULD be the signature verification key corresponding to the signing key.
      //# 
      //# If the algorithm suite does not contain a [signing algorithm](algorithm-suites.md#signature-algorithm):
      //# 
      //# - The CMM SHOULD NOT add a key-value pair using the reserved key `aws-crypto-public-key` to the encryption context.
      ensures output.Success?
      ==>
        && (
          output.value.encryptionMaterials.algorithmSuite.signature.ECDSA?
        <==>
          //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
          //= type=implication
          //# - The CMM MAY modify the encryption context.
          //
          //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
          //= type=implication
          //# If the algorithm suite contains a [signing algorithm](algorithm-suites.md#signature-algorithm),
          //# the default CMM MUST Add the key-value pair of
          //# key `aws-crypto-public-key`,
          //# value `base64-encoded public verification key`
          //# to the [encryption context](structures.md#encryption-context).
          && Materials.EC_PUBLIC_KEY_FIELD in output.value.encryptionMaterials.encryptionContext
          //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
          //= type=implication
          //# If the algorithm suite contains a [signing algorithm](algorithm-suites.md#signature-algorithm),
          //# the default CMM MUST Generate a [signing key](structures.md#signing-key).
          && output.value.encryptionMaterials.signingKey.Some?
        )

      //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
      //= type=implication
      //# If the encryption context included in the [encryption materials request](cmm-interface.md#encryption-materials-request)
      //# already contains the `aws-crypto-public-key` key,
      //# this operation MUST fail rather than overwrite the associated value.
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> output.Failure?

      // Make sure that we returned the correct algorithm suite, either as specified in
      // the input or, if that was not given, the default for the provided commitment policy
      ensures
        && output.Success?
      ==>
        (if input.algorithmSuiteId.Some? then
          //= aws-encryption-sdk-specification/framework/cmm-interface.md#get-encryption-materials
          //= type=implication
          //# - If the encryption materials request contains an algorithm suite, the encryption materials returned
          //# SHOULD contain the same algorithm suite.
          //
          //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
          //= type=implication
          //# - If the [encryption materials request](cmm-interface.md#encryption-
          //# materials-request) does contain an algorithm suite, the encryption
          //# materials returned MUST contain the same algorithm suite.
          output.value.encryptionMaterials.algorithmSuite.id == input.algorithmSuiteId.value
        else
            //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
            //= type=implication
            //# - If the [encryption materials request](cmm-interface.md#encryption-
            //# materials-request) does not contain an algorithm suite, the
            //# operation MUST add the default algorithm suite for the [commitment
            //# policy](./commitment-policy.md#supported-commitment-policy-enum) as the
            //# algorithm suite in the encryption materials returned.
            && input.algorithmSuiteId.None?
            && output.value.encryptionMaterials.algorithmSuite.id
              == Defaults.GetAlgorithmSuiteForCommitmentPolicy(input.commitmentPolicy))

      ensures
        && output.Success?
      ==>
        && |keyring.History.OnEncrypt| == |old(keyring.History.OnEncrypt)| + 1
        //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
        //= type=implication
        //# On each call to Get Encryption Materials,
        //# the default CMM MUST make a call to its [keyring's](#keyring)
        //# [On Encrypt](keyring-interface.md#onencrypt) operation.
        && Seq.Last(keyring.History.OnEncrypt).output.Success?
        //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
        //= type=implication
        //# The default CMM MUST obtain the Plaintext Data Key from the
        //# On Encrypt Response and include it in the
        //# [encryption materials](structures.md#encryption-materials) returned.
        && Seq.Last(keyring.History.OnEncrypt).output.value.materials.plaintextDataKey
        == output.value.encryptionMaterials.plaintextDataKey
        //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
        //= type=implication
        //# The default CMM MUST obtain the
        //# [Encrypted Data Keys](structures.md#encrypted-data-keys)
        //# from the On Encrypt Response and include it
        //# in the [encryption materials](structures.md#encryption-materials) returned.
        && Seq.Last(keyring.History.OnEncrypt).output.value.materials.encryptedDataKeys
        == output.value.encryptionMaterials.encryptedDataKeys

      //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
      //= type=implication
      //# - If the [encryption materials request](cmm-interface.md#encryption-
      //# materials-request) does contain an algorithm suite, the request
      //# MUST fail if the algorithm suite is not supported by the
      //# [commitment policy](./commitment-policy.md#supported-commitment-policy-enum) on
      //# the request.
      ensures
        && input.algorithmSuiteId.Some?
        && Commitment.ValidateCommitmentPolicyOnEncrypt(input.algorithmSuiteId.value, input.commitmentPolicy).Fail?
      ==>
        output.Failure?
    {
      :- Need(Materials.EC_PUBLIC_KEY_FIELD !in input.encryptionContext,
        Types.AwsCryptographicMaterialProvidersException(
          message :="Reserved Field found in EncryptionContext keys."));

      var algorithmId := if input.algorithmSuiteId.Some? then
        input.algorithmSuiteId.value
      else
        Defaults.GetAlgorithmSuiteForCommitmentPolicy(input.commitmentPolicy);

      :- Commitment.ValidateCommitmentPolicyOnEncrypt(
        algorithmId, input.commitmentPolicy
      );

      var suite := AlgorithmSuites.GetSuite(algorithmId);
      var signingKey: Option<seq<uint8>>;
      var verificationKey: Option<seq<uint8>>;
      if suite.signature.ECDSA? {
        var maybeECDSAPair := cryptoPrimitives.GenerateECDSASignatureKey(
          Crypto.GenerateECDSASignatureKeyInput(
            signatureAlgorithm := suite.signature.ECDSA.curve
          )
        );
        var pair :- maybeECDSAPair.MapFailure(e => Types.AwsCryptographyPrimitives(e));
        signingKey := Some(pair.signingKey);
        verificationKey := Some(pair.verificationKey);
      } else {
        assert  suite.signature.None?;
        signingKey := None;
        verificationKey := None;
      }

      var materials :- Materials.InitializeEncryptionMaterials(
        Types.InitializeEncryptionMaterialsInput(
          algorithmSuiteId := algorithmId,
          //= aws-encryption-sdk-specification/framework/default-cmm.md#get-encryption-materials
          //# Adding the key `aws-crypto-public-key` SHOULD be done to a copy of the encryption context
          //# so that the caller's encryption context is not mutated.
          encryptionContext := input.encryptionContext,
          signingKey := signingKey,
          verificationKey := verificationKey,
          requiredEncryptionContextKeys := input.requiredEncryptionContextKeys.UnwrapOr([])
        )
      );

      var result :- keyring.OnEncrypt(Types.OnEncryptInput(materials:=materials));
      var encryptionMaterialsOutput := Types.GetEncryptionMaterialsOutput(encryptionMaterials:=result.materials);

      :- Need(
        Materials.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOutput.encryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Could not retrieve materials required for encryption"));

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.ValidEncryptionMaterialsTransition(materials, encryptionMaterialsOutput.encryptionMaterials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring returned an invalid response"));

      output := Success(encryptionMaterialsOutput);
    }

    predicate DecryptMaterialsEnsuresPublicly(input: Types.DecryptMaterialsInput, output: Result<Types.DecryptMaterialsOutput, Types.Error>)
    {true}

    // The following are requirements for the CMM interface.
    // However they are requirments of intent
    // rather than something that can be verified programaticly.
    // The configured keyring could violate these properties.
    // This is why these are listed as exception and not implications.
    //
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
    //= type=exception
    //# When the CMM gets a [decrypt materials request](#decrypt-materials-request),
    //# it MUST return [decryption materials](structures.md#decryption-materials) appropriate for the request.
    //
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
    //= type=exception
    //# - The CMM MAY modify the encryption context.
    //
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
    //= type=exception
    //# - The plaintext data key returned MUST correspond with at least one of the encrypted data keys.
    //
    //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
    //= type=exception
    //# - The operations made on the encryption context on the Get Encryption Materials call
    //# SHOULD be inverted on the Decrypt Materials call.

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

      // if the output materials are valid then they contain the required fields
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# The decryption materials returned MUST include the following:

      // See DecryptionMaterialsWithPlaintextDataKey for details
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# - All keys in this set MUST exist in the decryption materials encryption context.
      //
      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# The CMM MUST ensure that the decryption materials returned are valid.
      //# - The decryption materials returned MUST follow the specification for [decryption-materials](structures.md#decryption-materials).
      //# - The value of the plaintext data key MUST be non-NULL.
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

      //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
      //= type=implication
      //# If the requested algorithm suite does not include a signing algorithm
      //# but the encryption context includes the reserved `aws-crypto-public-key` key, the operation SHOULD fail.
      //# Likewise, if the requested algorithm suite includes a signing algorithm
      //# but the encryption context does not include the reserved `aws-crypto-public-key` key, the operation SHOULD fail.
      //
      //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
      //= type=implication
      //# If this key is not present in the encryption context, the operation MUST fail
      //# without returning any decryption materials.
      //
      //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
      //= type=implication
      //# If the algorithm suite does not contain a [signing algorithm](algorithm-suites.md#signature-algorithm),
      //# but the encryption context includes the reserved `aws-crypto-public-key` key,
      //# the operation MUST fail without returning any decryption materials.
      ensures
        (
          AlgorithmSuites.GetSuite(input.algorithmSuiteId).signature.None?
          <==>
          (Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext + input.reproducedEncryptionContext.UnwrapOr(map[]))
        )
        ==> output.Failure?

      //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
      //= type=implication
      //# The request MUST fail if the algorithm suite on the request is not
      //# supported by the [commitment policy](./commitment-policy.md#supported-commitment-policy-enum)
      //# on the request.
      ensures Commitment.ValidateCommitmentPolicyOnDecrypt(input.algorithmSuiteId, input.commitmentPolicy).Fail?
      ==>
        output.Failure?

      //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
      //= type=implication
      //# If the algorithm suite contains a [signing algorithm](algorithm-suites.md#signature-algorithm),
      //# the default CMM MUST extract the verification key
      //# from the encryption context under the reserved `aws-crypto-public-key` key.
      ensures
        && output.Success?
        && AlgorithmSuites.GetSuite(input.algorithmSuiteId).signature.ECDSA?
      ==>
        && Materials.DecodeVerificationKey(input.encryptionContext + input.reproducedEncryptionContext.UnwrapOr(map[])).Success?
        && output.value.decryptionMaterials.verificationKey.Some?
        && output.value.decryptionMaterials.verificationKey
        == Some(Materials.DecodeVerificationKey(input.encryptionContext + input.reproducedEncryptionContext.UnwrapOr(map[])).value.value)

      ensures output.Success?
      ==>
        //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
        //= type=implication
        //# - If the decrypt materials request contains an algorithm suite,
        //# the decryption materials returned SHOULD contain the same algorithm suite.
        && input.algorithmSuiteId == output.value.decryptionMaterials.algorithmSuite.id
        //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
        //= type=implication
        //# If the algorithm suite obtained from the decryption request contains a [signing algorithm](algorithm-suites.md#signature-algorithm),
        //# the decryption materials MUST include the [signature verification key](structures.md#verification-key).
        && (output.value.decryptionMaterials.algorithmSuite.signature.ECDSA? ==> output.value.decryptionMaterials.verificationKey.Some?)

        && (0 < |output.value.decryptionMaterials.requiredEncryptionContextKeys| ==> input.reproducedEncryptionContext.Some?)
        //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials
        //= type=implication
        //# - This set MUST include all keys added to the decryption materials encryption context
        //# that existed in the [decrypt materials request's](#decrypt-materials-request) reproduced encryption context
        //# but did not exist in the [decrypt materials request's](#decrypt-materials-request) encryption context.
        && (forall key <- output.value.decryptionMaterials.requiredEncryptionContextKeys
          ::
            && key !in input.encryptionContext
            && key in input.reproducedEncryptionContext.value)

      ensures
        && output.Success?
      ==>
        && |keyring.History.OnDecrypt| == |old(keyring.History.OnDecrypt)| + 1
        //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
        //= type=implication
        //# On each call to Decrypt Materials,
        //# the default CMM MUST make a call to its [keyring's](#keyring)
        //# [On Decrypt](keyring-interface.md#ondecrypt) operation.
        && Seq.Last(keyring.History.OnDecrypt).output.Success?
        //= aws-encryption-sdk-specification/framework/default-cmm.md#decrypt-materials
        //= type=implication
        //# The default CMM MUST obtain the Plaintext Data Key from
        //# the On Decrypt response and include it in the decrypt
        //# materials returned.
        && Seq.Last(keyring.History.OnDecrypt).output.value.materials.plaintextDataKey
        == output.value.decryptionMaterials.plaintextDataKey

    {
      :- Commitment.ValidateCommitmentPolicyOnDecrypt(
        input.algorithmSuiteId, input.commitmentPolicy
      );

      var requiredEncryptionContextKeys := [];
      if input.reproducedEncryptionContext.Some? {
        var keysSet := input.reproducedEncryptionContext.value.Keys;
        while keysSet != {}
          invariant forall key
          |
            && key in input.reproducedEncryptionContext.value
            && key in input.encryptionContext
            && key !in keysSet
          :: input.reproducedEncryptionContext.value[key] == input.encryptionContext[key]
          invariant forall key <- requiredEncryptionContextKeys
          :: key !in input.encryptionContext
        {
          var key :| key in keysSet;
          if key in input.encryptionContext {
            :- Need(input.reproducedEncryptionContext.value[key] == input.encryptionContext[key],
              Types.AwsCryptographicMaterialProvidersException(
              message := "Encryption context does not match reproduced encryption context."));
          } else {
            requiredEncryptionContextKeys :=  requiredEncryptionContextKeys + [key];
          }
          keysSet := keysSet - {key};
        }
      }
    
      var materials :- Materials.InitializeDecryptionMaterials(
        Types.InitializeDecryptionMaterialsInput(
          algorithmSuiteId := input.algorithmSuiteId,
          encryptionContext := input.encryptionContext + input.reproducedEncryptionContext.UnwrapOr(map[]),
          requiredEncryptionContextKeys := requiredEncryptionContextKeys
        )
      );

      var result :- keyring.OnDecrypt(Types.OnDecryptInput(
        materials:=materials,
        encryptedDataKeys:=input.encryptedDataKeys
      ));

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.DecryptionMaterialsTransitionIsValid(materials, result.materials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring.OnDecrypt failed to decrypt the plaintext data key."));

      return Success(Types.DecryptMaterialsOutput(decryptionMaterials:=result.materials));
    }
  }
}
