include "../MessageHeader/Definitions.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/GenBytes.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Common.dfy"

module AESKeyringDef {
    import opened KeyringDefs
    import opened StandardLibrary
    import opened UInt = StandardLibrary.UInt
    import opened Cipher
    import GenBytes = RNG
    import AlgorithmSuite
    import AES = AESEncryption
    import opened SDKDefs

    class AESKeyring extends Keyring {
        const key_namespace : seq<uint8>
        const key_name : seq<uint8>
        const wrapping_key : seq<uint8>
        const aes_type : CipherParams

        predicate Valid() reads this {
            Repr == {this} &&
            (|wrapping_key| == KeyLengthOfCipher(aes_type)) &&
            (aes_type in {AES_GCM_128, AES_GCM_192, AES_GCM_256})
        }

        constructor(namespace : seq<uint8>, name : seq<uint8>, key : seq<uint8>, params : CipherParams)
        requires params in {AES_GCM_128, AES_GCM_192, AES_GCM_256}
        requires |key| == KeyLengthOfCipher(params)
        ensures key_namespace == namespace
        ensures key_name == name
        ensures wrapping_key == key
        ensures aes_type == params
        ensures aes_type in {AES_GCM_128, AES_GCM_192, AES_GCM_256}
        ensures Valid()
        {
            key_namespace := namespace;
            key_name := name;
            wrapping_key := key;
           aes_type := params;
           Repr := {this};
        }

        function method aes_provider_info(iv : seq<uint8>) : seq<uint8>
            requires |iv| == 12
            reads this {
              key_name +
                [0, 0, 0, TAG_LEN * 8] + // tag length in bits
                [0, 0, 0, IV_LEN] + // IV length in bytes
                iv
            }

        method OnEncrypt(x : EncMaterials) returns (res : Result<EncMaterials>)
            requires WFEncMaterials(x)
            requires Valid() ensures Valid()
            ensures res.Ok? ==> WFEncMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
        {
            var data_key := x.data_key;
            var alg_id := x.alg_id;
            if data_key.None? {
                var k := RNG.GenBytes(AlgorithmSuite.input_key_length(alg_id) as uint16);
                data_key := Some(k);
            }
            var iv := GenIV(aes_type);
            var aad := FlattenSortEncCtx(x.enc_ctx);
            var edk_ctxt := AES.AES.aes_encrypt(aes_type, iv, wrapping_key, data_key.get, aad);
            if edk_ctxt.Err? { return Err("Error on encrypt!"); }
            var provider_id := key_namespace;
            var provider_info := aes_provider_info(iv);
            return Ok(EncMat((alg_id), [EDK(provider_id, provider_info, edk_ctxt.get)] + x.edks, x.enc_ctx, data_key, None));
        }

        function method parse_provider_info(info : seq<uint8>) : Option<seq<uint8>> // returns the IV in the provider info, if it's of the right shape and key name is good
        {
            if |info| != |key_name| + 4 + 4 + 12 then None else
            if info[0..|key_name|] != key_name then None else
            Some (info[|key_name| + 8 ..])
        }

        method OnDecrypt(x : DecMaterials, edks : seq<EDK>) returns (res : Result<DecMaterials>)
            requires Valid()
            requires WFDecMaterials(x)
            ensures Valid()
            ensures res.Ok? ==> WFDecMaterials(res.get)
            ensures res.Ok? ==> res.get.alg_id == x.alg_id
        {
            if |edks| == 0 { return Err("No edks given to OnDecrypt!"); }
            if edks[0].provider_id != key_namespace { var x := OnDecrypt(x, edks[1..]); return x;}
            match parse_provider_info(edks[0].provider_info) {
                case None => {var x := OnDecrypt(x, edks[1..]); return x;}
                case Some(iv) => {
                    var octxt := AES.AES.aes_decrypt(aes_type, TAG_LEN, wrapping_key, edks[0].ciphertext, iv, EncCtxFlatten(x.enc_ctx));
                    match octxt {
                        case Err(e) => {var x := OnDecrypt(x, edks[1..]); return x;}
                        case Ok(k) => {
                            if |k| == AlgorithmSuite.input_key_length(x.alg_id) { // check for correct key length
                                return Ok(DecMat(x.alg_id, x.enc_ctx, Some(k), None));
                            }
                            else {
                                return Err("Bad key length!");
                            }
                        }
                    }
                }
            }
        }

    }
}
