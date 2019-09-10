include "CMM/Defs.dfy"
include "CMM/DefaultCMM.dfy"
include "Keyring/Defs.dfy"
include "Keyring/Defs.dfy"
include "Materials.dfy"
include "AlgorithmSuite.dfy"
include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/Cipher.dfy"

module ToyClientDef {
    import opened SDKDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import DefaultCMMDef
    import Keyring = KeyringDefs
    import CMM = CMMDefs
    import Alg = AlgorithmSuite
    import AES = AESEncryption
    import C = Cipher

    datatype Encryption = Encryption(ec : EncCtx, edks : seq<EDK>, ctxt : seq<uint8>)

    class ToyClient {
        var cmm : CMM.CMM
        ghost var Repr : set<object>
        predicate Valid() reads this, Repr {
            this in Repr &&
            cmm in Repr &&
            Repr == {this, cmm} + cmm.Repr &&
            cmm.Valid()
        }
        constructor OfCMM(c : CMM.CMM) requires c.Valid() ensures Valid() {
            cmm := c;
            new;
            Repr := {this, cmm} + cmm.Repr;
        } 
        constructor OfKeyring(k : Keyring.Keyring) requires k.Valid() ensures Valid() ensures fresh(cmm) {
            cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(k);
            new;
            Repr := {this, cmm} + cmm.Repr;
        } 
        method GetEncMaterials(ec : EncCtx) returns (res : Result<EncMaterials>) requires Valid() ensures Valid()
            ensures res.Ok? ==> res.get.alg_id == (Alg.AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384)
            ensures res.Ok? ==> res.get.data_key.Some?
        {
            res := cmm.EncMatRequest(ec, None, None);
            if res.Ok? {
                var r := res.get;
                if r.alg_id != (Alg.AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384) {
                    res := Err("bad alg id");
                }
                if r.data_key.None? {
                    res := Err("bad data key");
                }
            }
            else {
                return Err(res.err);
            }
        }

        method Enc(pt : seq<uint8>, ec : EncCtx) returns (res : Result<(Encryption)>) requires Valid() ensures Valid()
        {
            var oem := GetEncMaterials(ec);
            match oem {
                case Ok (em) => {
                    if |em.data_key.get| == 32 {
                        var ctxt := AES.AES.AESEncrypt(C.AES_GCM_256, (em.data_key.get), (pt), ([]));
                        if ctxt.Ok? {
                            return Ok(Encryption(em.enc_ctx, em.edks, ctxt.get));
                        }
                        else {
                            return Err("bad ctxt in Enc");
                        }
                    }
                    else { return Err("bad data key length"); }

                }
                case Err(e) => {return Err(e);}
            }
        }

        method Dec(e : Encryption) returns (res : Result<seq<uint8>>) requires Valid() ensures Valid()
        {
            if |e.edks| == 0 {
                return Err("no edks");
            }
            var odecmat := cmm.DecMatRequest(Alg.AES_256_GCM_IV12_AUTH16_KDSHA384_SIGEC384, e.edks, e.ec);
            match odecmat {
                case Ok(decmat) => {
                    match decmat.data_key {
                        case Some(dk) => {
                            if |dk| == 32 && |e.ctxt| > 12 {
                                var msg := AES.AES.AESDecrypt(C.AES_GCM_256, (dk), ([]), (e.ctxt));
                                return msg;
                            }
                            else {
                                return Err("bad dk");
                            }
                        }
                        case None => {
                            return Err("no dk?");
                        }
                    }

                }
                case Err(e) => {
                    return Err(e);
                }
            }
        }


    }

}
