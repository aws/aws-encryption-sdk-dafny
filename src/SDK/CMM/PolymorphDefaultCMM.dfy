// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "../EncryptionContext.dfy"
include "Defs.dfy"
include "../Keyring/Defs.dfy"
include "../MessageHeader.dfy"
include "../../Util/UTF8.dfy"
include "../Deserialize.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "PolymorphDefaultCMMDef"} PolymorphDefaultCMMDef {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Materials
  import EncryptionContext
  import CMMDefs
  import KeyringDefs
  import AlgorithmSuite
  import Signature
  import Base64
  import MessageHeader
  import UTF8
  import Deserialize
  import Aws.Crypto

  predicate {:opaque } DecryptionMaterialsFromPolymorphDefaultCMM(key: seq<uint8>)
  {
    true
  }

  // TODO move
  predicate method Serializable(mat:Crypto.EncryptionMaterials) {
    && |mat.encryptedDataKeys| > 0
    && EncryptionContext.Serializable(mat.encryptionContext)
  }

  class PolymorphDefaultCMM extends Crypto.ICryptographicMaterialsManager {
    const keyring: Crypto.IKeyring

    predicate method Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      keyring in Repr && keyring.Repr <= Repr && this !in keyring.Repr && keyring.Valid()
    }

    constructor OfKeyring(k: Crypto.IKeyring)
      requires k.Valid()
      ensures keyring == k
      ensures Valid() && fresh(Repr - k.Repr)
    {
      keyring := k;
      Repr := {this} + k.Repr;
    }

    method GetEncryptionMaterials(input: Crypto.GetEncryptionMaterialsInput)
                                  returns (res: Result<Crypto.GetEncryptionMaterialsOutput, string>)
      requires input.Valid()
      ensures Valid()
      // the heck is this?
      // ensures res.Success? ==> CMMDefs.EncryptionMaterialsSignature(res.value.materials)
      ensures res.Success? ==> res.value.materials.plaintextDataKey.Some? && Serializable(res.value.materials)
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> res.Failure?
      ensures res.Success? && (input.algorithmSuiteID.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteID.value).SignatureType().Some?) ==>
        Materials.EC_PUBLIC_KEY_FIELD in res.value.materials.encryptionContext
      ensures res.Success? ==> Serializable(res.value.materials)
      ensures res.Success? ==>
        match input.algorithmSuiteID
        case Some(id) => res.value.materials.algorithmSuiteID == id
        case None => AlgorithmSuite.PolymorphIDToInternalID(res.value.materials.algorithmSuiteID) == 0x0378
    {
      expect Valid();
      // reveal CMMDefs.EncryptionMaterialsSignatureOpaque();
      var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
      assert reservedField in Materials.RESERVED_KEY_VALUES;
      if reservedField in input.encryptionContext.Keys {
        return Failure("Reserved Field found in EncryptionContext keys.");
      }
      var id := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      if (input.algorithmSuiteID.Some?) {
        id := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteID.value);
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
        algorithmSuiteID:=AlgorithmSuite.InternalIDToPolymorphID(id),
        plaintextDataKey:=None(),
        encryptedDataKeys:=[],
        signingKey:=enc_sk
      );
      assert materials.encryptionContext == enc_ctx;
      var result :- keyring.OnEncrypt(Crypto.OnEncryptInput(materials:=materials));
      if result.materials.plaintextDataKey.None? || |result.materials.encryptedDataKeys| == 0 {
        return Failure("Could not retrieve materials required for encryption");
      }
      assert result.materials.Valid();

      expect result.materials.plaintextDataKey.Some? && Serializable(result.materials);
      expect (input.algorithmSuiteID.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteID.value).SignatureType().Some?) ==> Materials.EC_PUBLIC_KEY_FIELD in result.materials.encryptionContext;
      expect match input.algorithmSuiteID
        case Some(id) => result.materials.algorithmSuiteID == id
        case None => AlgorithmSuite.PolymorphIDToInternalID(result.materials.algorithmSuiteID) == 0x0378;

      return Success(Crypto.GetEncryptionMaterialsOutput(materials:=result.materials));
    }

    method DecryptMaterials(input: Crypto.DecryptMaterialsInput)
                            returns (res: Result<Crypto.DecryptMaterialsOutput, string>)
      requires input.Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.decryptionMaterials.plaintextDataKey.Some?
    {
      expect Valid();
      // Retrieve and decode verification key from encryption context if using signing algorithm
      var vkey := None;
      var algID := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteID);
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
        algorithmSuiteID:=input.algorithmSuiteID,
        plaintextDataKey:=None(),
        verificationKey:=vkey
      );
      var result :- keyring.OnDecrypt(Crypto.OnDecryptInput(materials:=materials, encryptedDataKeys:=input.encryptedDataKeys));
      if result.materials.plaintextDataKey.None? {
        return Failure("Keyring.OnDecrypt failed to decrypt the plaintext data key.");
      }

      return Success(Crypto.DecryptMaterialsOutput(decryptionMaterials:=result.materials));
    }
  }
}
