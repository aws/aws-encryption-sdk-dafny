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

    method EncMatRequest(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()
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

      var in_enc_mat := new Materials.EncryptionMaterials(id, [], enc_ec, None, enc_sk);
      res := kr.OnEncrypt(in_enc_mat);
    }

    method DecMatRequest(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) returns (res: Result<Materials.DecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid()
    {
      var vkey := Materials.enc_ctx_lookup(enc_ctx, Materials.EC_PUBLIC_KEY_FIELD);
      var dec_mat := new Materials.DecryptionMaterials(alg_id, enc_ctx, None, vkey);
      var dm :- kr.OnDecrypt(dec_mat, edks);
      match dm.algorithmSuiteID.SignatureType()
      case None =>
        return Success(dm);
      case Some(param) =>
        match Materials.enc_ctx_lookup(dm.encryptionContext, Materials.EC_PUBLIC_KEY_FIELD)
        case None =>
          return Failure("Public key field not found in encryption context!");
        case Some(pk) =>
          var decMat := new Materials.DecryptionMaterials(dm.algorithmSuiteID, dm.encryptionContext, dm.plaintextDataKey, Some(pk));
          return Success(decMat);
    }
  }
}

