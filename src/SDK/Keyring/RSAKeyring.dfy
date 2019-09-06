include "../MessageHeader/Definitions.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/GenBytes.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../Common.dfy"

module RSAKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened Cipher
    import GenBytes = RNG
    import AlgorithmSuite
    import RSA = RSAEncryption
    import opened SDKDefs

    class RSAKeyring extends Keyring {
        const key_namespace : seq<uint8>
        const key_name : seq<uint8>
        const rsa_params : (RSA.RSAPaddingMode, RSA.RSABitLength)
        const enc_key : Option<seq<uint8>>
        const dec_key : Option<seq<uint8>>

        predicate Valid() reads this {
            Repr == {this} &&
            (enc_key.Some? ==> RSA.RSA.RSAWfEK(rsa_params.1, rsa_params.0, enc_key.get)) &&
            (dec_key.Some? ==> RSA.RSA.RSAWfDK(rsa_params.1, rsa_params.0, dec_key.get)) &&
            (enc_key.Some? || dec_key.Some?)
        }

        constructor(namespace : seq<uint8>, name : seq<uint8>, padding : RSA.RSAPaddingMode, bits : RSA.RSABitLength, ek: Option<seq<uint8>>, dk: Option<seq<uint8>>)
            requires ek.Some? ==> RSA.RSA.RSAWfEK(bits, padding, ek.get)
            requires dk.Some? ==> RSA.RSA.RSAWfDK(bits, padding, dk.get)
            requires (ek.Some? || dk.Some?)
            ensures key_namespace == namespace
            ensures key_name == name
            ensures rsa_params == (padding, bits)
            ensures enc_key == ek
            ensures dec_key == dk
            ensures Valid()
        {
            key_namespace := namespace;
            key_name := name;
            rsa_params := (padding, bits);
            enc_key := ek;
            dec_key := dk;
            Repr := {this};
        }

        method OnEncrypt(x : EncMaterials) returns (res : Result<EncMaterials>)
            requires WFEncMaterials(x)
            requires Valid() ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
            ensures enc_key.None? ==> res.Err?
        {
            if enc_key.None? {
                res := Err("Encryption key undefined");
            }
            else {
                var data_key := x.data_key;
                var alg_id := x.alg_id;
                if data_key.None? {
                    var k := RNG.GenBytes(AlgorithmSuite.input_key_length(alg_id) as uint16);
                    data_key := Some(k);
                }
                var aad := FlattenSortEncCtx(x.enc_ctx);
                var edk_ctxt := RSA.RSA.RSAEncrypt(rsa_params.1, rsa_params.0, enc_key.get, data_key.get);
                if edk_ctxt.None? { return Err("Error on encrypt!"); }
                var provider_id := key_namespace;
                var provider_info := key_name;
                return Ok(EncMat((alg_id), [EDK(provider_id, provider_info, edk_ctxt.get)] + x.edks, x.enc_ctx, data_key, None));

            }

        }


        method OnDecrypt(x : DecMaterials, edks : seq<EDK>) returns (res : Result<DecMaterials>)
            requires Valid()
            requires WFDecMaterials(x)
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
            ensures dec_key.None? ==> res.Err?
        {
            if dec_key.None? { return Err(("Decryption key undefined"));}
            if |edks| == 0 { return Err(("Ran out of edks")); }
            if edks[0].provider_id != key_namespace { var x := OnDecrypt(x, edks[1..]); return x;}
            if edks[0].provider_info != key_name { var x := OnDecrypt(x, edks[1..]); return x;}
            var octxt := RSA.RSA.RSADecrypt(rsa_params.1, rsa_params.0, dec_key.get, edks[0].ciphertext);
            match octxt {
                    case None => {var x := OnDecrypt(x, edks[1..]); return x;}
                    case Some(k) => {
                            if |k| == AlgorithmSuite.input_key_length(x.alg_id) { // check for correct key length
                                return Ok(DecMat(x.alg_id, x.enc_ctx, Some(k), None));
                            }
                            else {
                                return Err(("Bad key length!"));
                            }
                    }

            }
        }


    }

}
