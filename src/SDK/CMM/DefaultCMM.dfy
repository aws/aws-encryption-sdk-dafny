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
      requires ValidAAD(ec) && ec.Keys !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? ==> |res.value.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.algorithmSuiteID.SignatureType()
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
          calc {
            |enc_vk|;
          ==  { assert UTF8.IsASCIIString(Base64.Encode(signatureKeys.verificationKey)); }
            |Base64.Encode(signatureKeys.verificationKey)|;
          <=  { Base64.EncodeLengthBound(signatureKeys.verificationKey); }
            |signatureKeys.verificationKey| / 3 * 4 + 4;
          <  { assert |signatureKeys.verificationKey| <= 3000; }
            UINT16_LIMIT;
          }

          var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
          assert reservedField in Materials.ReservedKeyValues;
          assert forall i :: i in ec.Keys ==> i != reservedField;
          enc_ctx := enc_ctx[reservedField := enc_vk];
          var len := MessageHeader.ComputeKVPairsLength(enc_ctx);
          if |enc_ctx| == UINT16_LIMIT {
            return Failure("encryption context has too many entries");
          }
          if UINT16_LIMIT <= len {
            return Failure("encryption context too big");
          }
          assert ValidAAD(enc_ctx) by {
            reveal MessageHeader.ValidAAD();
          }
      }

      var materials := Materials.EncryptionMaterials.WithoutDataKeys(enc_ctx, id, enc_sk);
      assert materials.encryptionContext == enc_ctx;
      materials :- kr.OnEncrypt(materials);
      if materials.plaintextDataKey.None? || |materials.encryptedDataKeys| == 0 {
        return Failure("Could not retrieve materials required for encryption");
      }
      assert materials.Valid();
      return Success(materials);
    }

    method DecryptMaterials(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) 
      returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
    {
      // Retrieve and decode verification key from encryption context if using signing algorithm
      var vkey := None;
      if alg_id.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        if reservedField !in enc_ctx {
          return Failure("Could not get materials required for decryption.");
        }
        var encodedVKey := enc_ctx[reservedField];
        var utf8Decoded :- UTF8.Decode(encodedVKey);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }

      var materials := Materials.DecryptionMaterials.WithoutPlaintextDataKey(enc_ctx, alg_id, vkey);
      materials :- kr.OnDecrypt(materials, edks);
      if materials.plaintextDataKey.None? {
        return Failure("Keyring.OnDecrypt failed to decrypt the plaintext data key.");
      }

      return Success(materials);
    }
  }
}

