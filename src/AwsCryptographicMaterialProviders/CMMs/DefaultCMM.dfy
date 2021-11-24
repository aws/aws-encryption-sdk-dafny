// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../CMM.dfy"
include "../../Util/UTF8.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.DefaultCMM"}
  MaterialProviders.DefaultCMM
{
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuites
  import Materials
  import CMM
  import Signature
  import Base64
  import UTF8
  import Aws.Crypto

  class DefaultCMM
    extends CMM.VerifiableInterface
  {
    const keyring: Crypto.IKeyring

    constructor OfKeyring(k: Crypto.IKeyring)
      ensures keyring == k
    {
      keyring := k;
    }

    method GetEncryptionMaterials(
      input: Crypto.GetEncryptionMaterialsInput
    )
      returns (res: Result<Crypto.GetEncryptionMaterialsOutput, string>)
      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsWithPlaintextDataKey(res.value.encryptionMaterials)
        // TODO Need to prove
        && (
          AlgorithmSuites.GetSuite(res.value.encryptionMaterials.algorithmSuiteId).signature.ECDSA?
        ==>
          Materials.EC_PUBLIC_KEY_FIELD in res.value.encryptionMaterials.encryptionContext
        )
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> res.Failure?
    {
      :- Need(
        Materials.EC_PUBLIC_KEY_FIELD !in input.encryptionContext,
        "Reserved Field found in EncryptionContext keys.");

      var id := input
        .algorithmSuiteId
        .UnwrapOr(Crypto.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384);

      var suite := AlgorithmSuites.GetSuite(id);
      var materials :- InitializeEncryptionMaterials(
        suite,
        input.encryptionContext
      );

      var result :- keyring.OnEncrypt(Crypto.OnEncryptInput(materials:=materials));
      :- Need(
        && result.materials.plaintextDataKey.Some?
        && |result.materials.encryptedDataKeys| > 0,
        "Could not retrieve materials required for encryption");

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.EncryptionMaterialsTransitionIsValid(materials, result.materials),
        "Keyring returned an invalid response");

      AlgorithmSuites.LemmaAlgorithmSuiteIdImpliesEquality(result.materials.algorithmSuiteId, suite);
      return Success(Crypto.GetEncryptionMaterialsOutput(encryptionMaterials:=result.materials));
    }

    method DecryptMaterials(
      input: Crypto.DecryptMaterialsInput
    )
      returns (res: Result<Crypto.DecryptMaterialsOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsWithPlaintextDataKey(res.value.decryptionMaterials)
    {

      var materials :- InitializeDecryptionMaterials(
        AlgorithmSuites.GetSuite(input.algorithmSuiteId),
        input.encryptionContext
      );

      var result :- keyring.OnDecrypt(Crypto.OnDecryptInput(
        materials:=materials,
        encryptedDataKeys:=input.encryptedDataKeys
      ));

      // For Dafny keyrings this is a trivial statement
      // because they implement a trait that ensures this.
      // However not all keyrings are Dafny keyrings.
      // Customers can create custom keyrings.
      :- Need(
        Materials.DecryptionMaterialsTransitionIsValid(materials, result.materials),
        "Keyring.OnDecrypt failed to decrypt the plaintext data key.");

      return Success(Crypto.DecryptMaterialsOutput(decryptionMaterials:=result.materials));
    }
  }

  method InitializeEncryptionMaterials(
    suite: AlgorithmSuites.AlgorithmSuite,
    encryptionContext: Crypto.EncryptionContext
  )
    returns (res: Result<Crypto.EncryptionMaterials, string>)
    requires Materials.EC_PUBLIC_KEY_FIELD !in encryptionContext
    ensures
      && res.Success?
    ==>
      && Materials.ValidEncryptionMaterials(res.value)
      && res.value.algorithmSuiteId == suite.id
      && (suite.signature.ECDSA? ==> Materials.EC_PUBLIC_KEY_FIELD in res.value.encryptionContext)
  {
    match suite.signature
      case None =>
        var mat := Crypto.EncryptionMaterials(
          encryptionContext := encryptionContext,
          algorithmSuiteId := suite.id,
          plaintextDataKey := None(),
          encryptedDataKeys := [],
          signingKey := None()
        );
        AlgorithmSuites.LemmaAlgorithmSuiteIdImpliesEquality(mat.algorithmSuiteId, suite);
        return Success(mat);
      case ECDSA(curve) =>
        var signatureKeys :- Signature.KeyGen(curve);
        var enc_vk :- UTF8.Encode(Base64.Encode(signatureKeys.verificationKey));
        var mat := Crypto.EncryptionMaterials(
          encryptionContext := encryptionContext[Materials.EC_PUBLIC_KEY_FIELD := enc_vk],
          algorithmSuiteId := suite.id,
          plaintextDataKey := None(),
          encryptedDataKeys := [],
          signingKey := Some(signatureKeys.signingKey)
        );
        AlgorithmSuites.LemmaAlgorithmSuiteIdImpliesEquality(mat.algorithmSuiteId, suite);
        return Success(mat);
  }

  method InitializeDecryptionMaterials(
      suite: AlgorithmSuites.AlgorithmSuite,
      encryptionContext: Crypto.EncryptionContext
    )
      returns (res: Result<Crypto.DecryptionMaterials, string>)
      ensures
        && res.Success?
      ==>
        && Materials.ValidDecryptionMaterials(res.value)
        && res.value.algorithmSuiteId == suite.id
    {
      match suite.signature
        case None =>
          :- Need(
            Materials.EC_PUBLIC_KEY_FIELD !in encryptionContext,
            "Verification key can not exist in non-signed Algorithm Suites.");
          var mat := Crypto.DecryptionMaterials(
            encryptionContext := encryptionContext,
            algorithmSuiteId := suite.id,
            plaintextDataKey := None(),
            verificationKey := None()
          );
        AlgorithmSuites.LemmaAlgorithmSuiteIdImpliesEquality(mat.algorithmSuiteId, suite);
        return Success(mat);
        case ECDSA(curve) =>
          :- Need(
            Materials.EC_PUBLIC_KEY_FIELD in encryptionContext,
            "Encryption Context missing verification key.");
          var encodedVerificationKey := encryptionContext[Materials.EC_PUBLIC_KEY_FIELD];
          var decodedUtf8VerificationKey :- UTF8.Decode(encodedVerificationKey);
          var base64DecodedVerificationKey :- Base64.Decode(decodedUtf8VerificationKey);
          var mat := Crypto.DecryptionMaterials(
            encryptionContext := encryptionContext,
            algorithmSuiteId := suite.id,
            plaintextDataKey := None(),
            verificationKey := Some(base64DecodedVerificationKey)
          );
          AlgorithmSuites.LemmaAlgorithmSuiteIdImpliesEquality(mat.algorithmSuiteId, suite);
          return Success(mat);
    }
}
