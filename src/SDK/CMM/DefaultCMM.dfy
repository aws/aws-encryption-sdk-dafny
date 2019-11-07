include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../Keyring/Defs.dfy"
include "../MessageHeader.dfy"
include "../../Util/UTF8.dfy"

module DefaultCMMDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMMDefs
  import KeyringDefs
  import AlgorithmSuite
  import S = Signature
  import Base64
  import MessageHeader
  import UTF8

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

    method GetEncryptionMaterials(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() &&
                               res.value.plaintextDataKey.Some? && 
                               |res.value.plaintextDataKey.get| == res.value.algorithmSuiteID.KDFInputKeyLength() &&
                               |res.value.encryptedDataKeys| > 0
      ensures res.Success? ==>
        match res.value.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some? &&
            S.ECDSA.WfSK(sigType, res.value.signingKey.get)
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
              var enc_vk :- UTF8.Encode(Base64.Encode(ab.0));
              var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
              enc_ec := [(reservedField, enc_vk)] + enc_ec;
      }

      MessageHeader.AssumeValidAAD(enc_ec);  // TODO: we should prove this
      var in_enc_mat := new Materials.EncryptionMaterials(id, [], enc_ec, None, enc_sk);
      var em :- kr.OnEncrypt(in_enc_mat);

      if em.plaintextDataKey.None? ||
         |em.plaintextDataKey.get| != em.algorithmSuiteID.KDFInputKeyLength() ||
         |em.encryptedDataKeys| == 0 ||
         (em.algorithmSuiteID.SignatureType().Some? && em.signingKey.None?)
      {
        return Failure("Could not retrieve materials required for encryption");
      }
      return Success(em);
    }

    method DecryptMaterials(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext) returns (res: Result<Materials.DecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() &&
                               res.value.plaintextDataKey.Some? &&
                               |res.value.plaintextDataKey.get| == res.value.algorithmSuiteID.KeyLength()
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
    {
      // Retrieve and decode verification key from encryption context if using signing algorithm
      var vkey := None;
      if alg_id.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        var encodedVKey := Materials.EncCtxLookup(enc_ctx, reservedField);
        if encodedVKey == None {
          return Failure("Could not get materials required for decryption.");
        }
        var utf8Decoded :- UTF8.Decode(encodedVKey.get);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }

      var dec_mat := new Materials.DecryptionMaterials(alg_id, enc_ctx, None, vkey);
      var dm :- kr.OnDecrypt(dec_mat, edks);

      if dm.plaintextDataKey.None? ||
         |dm.plaintextDataKey.get| != dm.algorithmSuiteID.KeyLength() ||
         (dm.algorithmSuiteID.SignatureType().Some? && |dm.plaintextDataKey.get| != dm.algorithmSuiteID.KeyLength()) {
        return Failure("Could not get materials required for decryption.");
      }

      return Success(dm);
    }
  }
}

