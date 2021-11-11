// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "../EncryptionContext.dfy"
include "../../Util/UTF8.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "DefaultCMMDef"} DefaultCMMDef {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Materials
  import EncryptionContext
  import AlgorithmSuite
  import Signature
  import Base64
  import UTF8
  import Aws.Crypto

  // TODO move somewhere central
  predicate method Serializable(mat:Crypto.EncryptionMaterials) {
    && |mat.encryptedDataKeys| > 0
    && EncryptionContext.Serializable(mat.encryptionContext)
  }

  // TODO: What are these predicates doing and should we reintroduce them? We can't ensure them on all CMM GetEncryptionMaterials calls anymore.
  // Predicate works arround a known error in Dafny: https://github.com/dafny-lang/dafny/issues/422
  // predicate EncryptionMaterialsSignature(validEncryptionMaterials: Crypto.EncryptionMaterials) {
  //  EncryptionMaterialsSignatureOpaque(validEncryptionMaterials)
  // }
  // predicate {:opaque } EncryptionMaterialsSignatureOpaque(validEncryptionMaterials: Crypto.EncryptionMaterials)
  // {
  //   true
  // }

  class DefaultCMM extends Crypto.ICryptographicMaterialsManager {
    const keyring: Crypto.IKeyring

    constructor OfKeyring(k: Crypto.IKeyring)
      ensures keyring == k
    {
      keyring := k;
    }

    method GetEncryptionMaterials(input: Crypto.GetEncryptionMaterialsInput)
                                  returns (res: Result<Crypto.GetEncryptionMaterialsOutput, string>)
      requires input.Valid()
      // TODO what is the history behind this predicate and should we reintroduce it?
      // ensures res.Success? ==> EncryptionMaterialsSignature(res.value.materials)
      ensures res.Success? ==> res.value.encryptionMaterials.plaintextDataKey.Some? && Serializable(res.value.encryptionMaterials)
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> res.Failure?
      ensures res.Success? && (input.algorithmSuiteId.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value).SignatureType().Some?) ==>
        Materials.EC_PUBLIC_KEY_FIELD in res.value.encryptionMaterials.encryptionContext
      ensures res.Success? ==> Serializable(res.value.encryptionMaterials)
      ensures res.Success? ==>
        match input.algorithmSuiteId
        case Some(id) => res.value.encryptionMaterials.algorithmSuiteId == id
        case None => AlgorithmSuite.PolymorphIDToInternalID(res.value.encryptionMaterials.algorithmSuiteId) == 0x0378
    {
      // reveal EncryptionMaterialsSignatureOpaque();
      var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
      assert reservedField in Materials.RESERVED_KEY_VALUES;
      if reservedField in input.encryptionContext.Keys {
        return Failure("Reserved Field found in EncryptionContext keys.");
      }
      var id := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      if (input.algorithmSuiteId.Some?) {
        id := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value);
      }
      var enc_sk := None;
      var enc_ctx := input.encryptionContext;

      match id.SignatureType() {
        case None =>
        case Some(param) =>
          var signatureKeys :- Signature.KeyGen(param);
          enc_sk := Some(signatureKeys.signingKey);
          var enc_vk :- UTF8.Encode(Base64.Encode(signatureKeys.verificationKey));
          enc_ctx := enc_ctx[reservedField := enc_vk];
      }

      // Check validity of the encryption context at runtime.
      var validAAD := EncryptionContext.CheckSerializable(enc_ctx);
      if !validAAD {
        //TODO: Provide a more specific error message here, depending on how the EncCtx spec was violated.
        return Failure("Invalid Encryption Context");
      }
      assert EncryptionContext.Serializable(enc_ctx);

      var materials := Crypto.EncryptionMaterials(
        encryptionContext:=enc_ctx,
        algorithmSuiteId:=AlgorithmSuite.InternalIDToPolymorphID(id),
        plaintextDataKey:=None(),
        encryptedDataKeys:=[],
        signingKey:=enc_sk
      );
      assert materials.encryptionContext == enc_ctx;
      var result :- keyring.OnEncrypt(Crypto.OnEncryptInput(materials:=materials));
      if result.materials.plaintextDataKey.None? || |result.materials.encryptedDataKeys| == 0 {
        return Failure("Could not retrieve materials required for encryption");
      }

      // TODO more informative error message
      :- Need(OnEncryptResultValid(input, result), "Keyring returned an invalid response");

      return Success(Crypto.GetEncryptionMaterialsOutput(encryptionMaterials:=result.materials));
    }

    method DecryptMaterials(input: Crypto.DecryptMaterialsInput)
                            returns (res: Result<Crypto.DecryptMaterialsOutput, string>)
      requires input.Valid()
      ensures res.Success? ==> res.value.decryptionMaterials.plaintextDataKey.Some?
    {
      // Retrieve and decode verification key from encryption context if using signing algorithm
      var vkey := None;
      var algID := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId);
      var encCtx := input.encryptionContext;

      if algID.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        if reservedField !in encCtx {
          return Failure("Could not get materials required for decryption.");
        }
        var encodedVKey := encCtx[reservedField];
        var utf8Decoded :- UTF8.Decode(encodedVKey);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }

      var materials := Crypto.DecryptionMaterials(
        encryptionContext:=encCtx,
        algorithmSuiteId:=input.algorithmSuiteId,
        plaintextDataKey:=None(),
        verificationKey:=vkey
      );
      var result :- keyring.OnDecrypt(Crypto.OnDecryptInput(materials:=materials, encryptedDataKeys:=input.encryptedDataKeys));
      if result.materials.plaintextDataKey.None? {
        return Failure("Keyring.OnDecrypt failed to decrypt the plaintext data key.");
      }

      // TODO Why do we not need to check anything on the OnDecrypt result?

      return Success(Crypto.DecryptMaterialsOutput(decryptionMaterials:=result.materials));
    }

    // TODO move somewhere central
    predicate method OnEncryptResultValid(input: Crypto.GetEncryptionMaterialsInput, result: Crypto.OnEncryptOutput) {
      && (
        result.materials.plaintextDataKey.Some? && Serializable(result.materials))
      && (
        (input.algorithmSuiteId.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value).SignatureType().Some?) ==> Materials.EC_PUBLIC_KEY_FIELD in result.materials.encryptionContext)
      && (
      match input.algorithmSuiteId
        case Some(id) => result.materials.algorithmSuiteId == id
        case None => AlgorithmSuite.PolymorphIDToInternalID(result.materials.algorithmSuiteId) == 0x0378)
    }
  }
}
