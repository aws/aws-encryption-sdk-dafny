include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../Keyring/Defs.dfy"

module DefaultCMMDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMMDefs
  import KeyringDefs
  import AlgorithmSuite
  import S = Signature
  import Base64

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

    method GetEncryptionMaterials(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>) 
      returns (res: Result<Materials.ValidEncryptionMaterialsOutput>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()
      ensures res.Success? && alg_id.Some? ==> res.value.dataKey.algorithmSuiteID == alg_id.get
    {
      var id := if alg_id.Some? then alg_id.get else AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      var enc_sk := None;
      var enc_ec := ec;

      match id.SignatureType() {
        case None =>
        case Some(param) =>
          var oab := S.ECDSA.KeyGen(param);
          match oab
            case None => return Failure("Keygen error");
            case Some(ab) =>
              enc_sk := Some(ab.1);
              enc_ec := [(Materials.EC_PUBLIC_KEY_FIELD, StringToByteSeq(Base64.Encode(ab.1)))] + enc_ec;
      }

      var in_enc_mat := Materials.EncryptionMaterialsInput(id, enc_ec, None);
      var dataKey :- kr.OnEncrypt(in_enc_mat);
      if dataKey.None? {
        return Failure("Could not retrieve materials required for encryption");
      }
      Materials.ValidOnEncryptResultImpliesSameAlgorithmSuiteID(in_enc_mat, dataKey.get);
      return Success(Materials.EncryptionMaterialsOutput(dataKey.get, enc_sk));
    }

    method DecryptMaterials(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) 
      returns (res: Result<Materials.ValidDecryptionMaterialsOutput>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.dataKey.algorithmSuiteID == alg_id
    {
      var vkey := Materials.enc_ctx_lookup(enc_ctx, Materials.EC_PUBLIC_KEY_FIELD);
      var dm :- kr.OnDecrypt(alg_id, enc_ctx, edks);
      if dm.None? {
        return Failure("Could not get materials required for decryption.");
      }
      Materials.ValidOnDecryptResultImpliesSameAlgorithmSuiteID(alg_id, enc_ctx, edks, dm.get);

      var verificationKey := None;
      if dm.get.algorithmSuiteID.SignatureType().Some? {
        match Materials.enc_ctx_lookup(enc_ctx, Materials.EC_PUBLIC_KEY_FIELD)
        case None =>
          return Failure("Could not get materials required for decryption.");
        case Some(pk) =>
          verificationKey := Some(pk);
      }
      return Success(Materials.DecryptionMaterialsOutput(dm.get, verificationKey));
    }
  }
}

