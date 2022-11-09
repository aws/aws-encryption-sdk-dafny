// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/StandardLibrary/Base64.dfy"
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
      ensures output.Success?
      ==>
        && Materials.EncryptionMaterialsHasPlaintextDataKey(output.value.encryptionMaterials)
        && (
          output.value.encryptionMaterials.algorithmSuite.signature.ECDSA?
        <==>
          Materials.EC_PUBLIC_KEY_FIELD in output.value.encryptionMaterials.encryptionContext
        )
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> output.Failure?

      // Make sure that we returned the correct algorithm suite, either as specified in
      // the input or, if that was not given, the default for the provided commitment policy
      ensures
        && output.Success?
      ==>
        (if input.algorithmSuiteId.Some? then
          //= compliance/framework/default-cmm.txt#2.6.1
          //= type=implication
          //# *  If the encryption materials request (cmm-interface.md#encryption-
          //# materials-request) does contain an algorithm suite, the encryption
          //# materials returned MUST contain the same algorithm suite.
          output.value.encryptionMaterials.algorithmSuite.id == input.algorithmSuiteId.value
        else
            //= compliance/framework/default-cmm.txt#2.6.1
            //= type=implication
            //# *  If the encryption materials request (cmm-interface.md#encryption-
            //# materials-request) does not contain an algorithm suite, the
            //# operation MUST add the default algorithm suite for the commitment
            //# policy (../client-apis/client.md#commitment-policy) as the
            //# algorithm suite in the encryption materials returned.
            //
            //= compliance/client-apis/client.txt#2.4.2.1
            //= type=implication
            //# *  "03 78" MUST be the default algorithm suite
            //
            //= compliance/client-apis/client.txt#2.4.2.2
            //= type=implication
            //# *  "05 78" MUST be the default algorithm suite
            //
            //= compliance/client-apis/client.txt#2.4.2.3
            //= type=implication
            //# *  "05 78" MUST be the default algorithm suite
            && input.algorithmSuiteId.None?
            && output.value.encryptionMaterials.algorithmSuite.id
              == Defaults.GetAlgorithmSuiteForCommitmentPolicy(input.commitmentPolicy))

      //= compliance/framework/default-cmm.txt#2.6.1
      //= type=implication
      //# *  If the encryption materials request (cmm-interface.md#encryption-
      //# materials-request) does contain an algorithm suite, the request
      //# MUST fail if the algorithm suite is not supported by the
      //# commitment policy (../client-apis/client.md#commitment-policy) on
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
          encryptionContext := input.encryptionContext,
          signingKey := signingKey,
          verificationKey := verificationKey
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

      // If the input has either
      //   (a) an unsigned algorithm suite and the aws-crypto-public-key encryption context key
      //   (b) a signing algorithm suite and no aws-crypto-public-key encryption context key
      // then the operation SHOULD fail.
      // (Here we strengthen the SHOULD to a MUST.)
      ensures
        (
          AlgorithmSuites.GetSuite(input.algorithmSuiteId).signature.None?
          <==>
          (Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext)
        )
        ==> output.Failure?

      //= compliance/framework/default-cmm.txt#2.6.2
      //= type=implication
      //# The request MUST fail if the algorithm suite on the request is not
      //# supported by the commitment policy (../client-apis/
      //# client.md#commitment-policy) on the request.
      ensures Commitment.ValidateCommitmentPolicyOnDecrypt(input.algorithmSuiteId, input.commitmentPolicy).Fail?
      ==>
        output.Failure?
    {
      :- Commitment.ValidateCommitmentPolicyOnDecrypt(
        input.algorithmSuiteId, input.commitmentPolicy
      );

      var materials :- Materials.InitializeDecryptionMaterials(
        Types.InitializeDecryptionMaterialsInput(
          algorithmSuiteId := input.algorithmSuiteId,
          encryptionContext := input.encryptionContext
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
