include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../Keyring/Defs.dfy"
include "../MessageHeader.dfy"
include "../../Util/UTF8.dfy"
include "../Deserialize.dfy"

module {:extern "DefaultCMMDef"} DefaultCMMDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMMDefs
  import KeyringDefs
  import AlgorithmSuite
  import Signature
  import Base64
  import MessageHeader
  import UTF8
  import Deserialize

  class DefaultCMM extends CMMDefs.CMM {
    const kr: KeyringDefs.Keyring

    predicate Valid()
      reads this, Repr
    {
      kr in Repr &&
      Repr == {this, kr} + kr.Repr &&
      kr.Valid()
    }

    constructor OfKeyring(k: KeyringDefs.Keyring)
      requires k.Valid()
      ensures kr == k
      ensures Valid()
    {
      kr := k;
      Repr := {this, kr} + k.Repr;
    }

    method GetEncryptionMaterials(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(ec) && Materials.GetKeysFromEncryptionContext(ec) !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> res.value.dataKeyMaterials.algorithmSuiteID.ValidPlaintextDataKey(res.value.dataKeyMaterials.plaintextDataKey)
      ensures res.Success? ==> |res.value.dataKeyMaterials.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.dataKeyMaterials.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some?
    {
      var id := if alg_id.Some? then alg_id.get else AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      var enc_sk := None;
      var enc_ctx := ec;

      match id.SignatureType() {
        case None =>
        case Some(param) =>
          var signatureKeys :- Signature.KeyGen(param);
          enc_sk := Some(signatureKeys.signingKey);
          var enc_vk :- UTF8.Encode(Base64.Encode(signatureKeys.verificationKey));
          var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
          assert reservedField in Materials.ReservedKeyValues;
          assert forall i | 0 <= i < |ec| :: ec[i].0 != reservedField;
          assert MessageHeader.SortedKVPairs(enc_ctx) by { // this is a precondition of InsertNewEntry
            assert MessageHeader.ValidAAD(enc_ctx);
            reveal MessageHeader.ValidAAD();
          }
          // The following 3 lines should be combined into one, once this gets fixed: https://github.com/dafny-lang/dafny/issues/425
          var optionResult;
          ghost var insertionPoint;
          optionResult, insertionPoint := Deserialize.InsertNewEntry(enc_ctx, reservedField, enc_vk);
          enc_ctx := optionResult.get;
      }

      MessageHeader.AssumeValidAAD(enc_ctx);  // TODO: we should check this (https://github.com/awslabs/aws-encryption-sdk-dafny/issues/79)

      var dataKeyMaterials :- kr.OnEncrypt(id, enc_ctx, None);
      if dataKeyMaterials.None? || |dataKeyMaterials.get.encryptedDataKeys| == 0 {
        return Failure("Could not retrieve materials required for encryption");
      }
      return Success(Materials.EncryptionMaterials(enc_ctx, dataKeyMaterials.get, enc_sk));
    }

    method DecryptMaterials(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) 
      returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
    {
      // Retrieve and decode verification key from encryption context if using signing algorithm
      var vkey := None;
      if alg_id.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        var encodedVKey := Materials.EncryptionContextGet(enc_ctx, reservedField);
        if encodedVKey.Failure? {
          return Failure("Could not get materials required for decryption.");
        }
        var utf8Decoded :- UTF8.Decode(encodedVKey.value);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }

      var onDecryptResult :- kr.OnDecrypt(alg_id, enc_ctx, edks);
      if onDecryptResult.None? {
        return Failure("Keyring.OnDecrypt did not return a value.");
      }

      return Success(Materials.DecryptionMaterials(alg_id, enc_ctx, onDecryptResult.get.plaintextDataKey, vkey, onDecryptResult.get.keyringTrace));
    }
  }
}

