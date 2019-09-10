include "../Materials.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../../StandardLibrary/Base64.dfy"
include "./Defs.dfy"
include "../Keyring/Defs.dfy"
include "../../Crypto/Signature.dfy"

module DefaultCMMDef {
    import opened SDKDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import AlgorithmSuite
    import opened CMMDefs
    import KeyringDefs
    import S = Signature
    import Base64

    class DefaultCMM extends CMM {
        const kr : KeyringDefs.Keyring

        predicate Valid() reads this, Repr
        {
            kr in Repr &&
            Repr == {this, kr} + kr.Repr &&
            kr.Valid()
        }

        method EncMatRequest(ec : EncCtx, alg_id : Option<AlgorithmSuite.ID>, pt_len : Option<nat>) returns (res : Result<EncMaterials>)
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
        {
            var id;
            if alg_id.Some? {
                id := alg_id.get;
            }
            else {
                id := AlgorithmSuite.AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384;
            }

            var enc_sk := None;
            var enc_ec := ec;

            match AlgorithmSuite.signature_type_of_id(id) {
                case Some(param) =>  {
                    var oab := S.ECDSA.KeyGen(param);
                    match oab {
                        case None => { return Err("Keygen error");}
                        case Some(ab) => {
                            enc_sk := Some(ab.1);
                            enc_ec := [(EC_PUBLIC_KEY_FIELD, byteseq_of_string(Base64.Encode(ab.1)))] + enc_ec;
                        }
                    }
                }
                case None =>  { }
            }

            var in_enc_mat := EncMat(id, [], enc_ec, None, enc_sk);
            res := kr.OnEncrypt(in_enc_mat);
        }

        method DecMatRequest(alg_id : AlgorithmSuite.ID, edks : seq<EDK>, enc_ctx : EncCtx) returns (res : Result<DecMaterials>)
            requires |edks| > 0
            requires Valid()
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
        {
            var vkey := enc_ctx_lookup(enc_ctx, EC_PUBLIC_KEY_FIELD);
            var dec_mat := DecMat(alg_id, enc_ctx, None, vkey);
            var kr_res := kr.OnDecrypt(dec_mat, edks);
            match kr_res {
                case Ok(dm) => {
                    match AlgorithmSuite.signature_type_of_id(dm.alg_id) {
                        case Some(param) => {
                            match enc_ctx_lookup(dm.enc_ctx, EC_PUBLIC_KEY_FIELD) {
                                case Some(pk) => {
                                    return Ok(DecMat(dm.alg_id, dm.enc_ctx, dm.data_key, Some(pk)));
                                }
                                case None => {
                                    res := Err("Public key field not found in encryption context!");
                                }
                            }
                        }
                        case None => {
                            res := Ok(dm);
                        }
                    }
                }
                case Err(e) => {return Err(e);}
            }
        }
        
        constructor OfKeyring(k : KeyringDefs.Keyring) requires k.Valid() ensures kr == k ensures Valid() {
            kr := k;
            Repr := {this, kr} + k.Repr;
        }
    }
}

