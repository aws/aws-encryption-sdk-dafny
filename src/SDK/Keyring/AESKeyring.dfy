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
  import Mat = Materials

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

    constructor(namespace: seq<uint8>, name: seq<uint8>, key: seq<uint8>, params: CipherParams)
    requires params in {AES_GCM_128, AES_GCM_192, AES_GCM_256}
    requires |key| == KeyLengthOfCipher(params)
    ensures key_namespace == namespace
    ensures key_name == name
    ensures wrapping_key == key
    ensures aes_type == params
    ensures aes_type in {AES_GCM_128, AES_GCM_192, AES_GCM_256} //This seems redundant
    ensures Valid()
    {
      key_namespace := namespace;
      key_name := name;
      wrapping_key := key;
      aes_type := params;
      Repr := {this};
    }

    function method aes_provider_info(iv: seq<uint8>): seq<uint8>
      requires |iv| == 12
      reads this
    {
      key_name + 
        [0, 0, 0, TAG_LEN * 8] + // tag length in bits
        [0, 0, 0, IV_LEN] + // IV length in bytes
        iv
    }

    method OnEncrypt(x: Mat.EncryptionMaterials) returns (res: Result<Mat.EncryptionMaterials>)
      requires x.Valid()
      requires Valid() ensures Valid()
      modifies x`plaintextDataKey
      modifies x`encryptedDataKeys
      ensures res.Success? ==> res.value.Valid() && res.value == x
      ensures res.Success? && old(x.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(x.plaintextDataKey)
      ensures res.Failure? ==> unchanged(x)
    {
      var data_key := x.plaintextDataKey;
      var alg_id := x.algorithmSuiteID;
      if data_key.None? {
        var k := RNG.GenBytes(AlgorithmSuite.InputKeyLength(alg_id) as uint16);
        data_key := Some(k);
      }
      var iv := GenIV(aes_type);
      var aad := if x.encryptionContext.Some?
                 then Mat.FlattenSortEncCtx(x.encryptionContext.get)
                 else []; //FIXME this is a hack, and I hate it.
      var edk_ctxt := AES.AES.aes_encrypt(aes_type, iv, wrapping_key, data_key.get, aad);
      if edk_ctxt.Failure? { return Failure("Error on encrypt!"); }
      var provider_info := aes_provider_info(iv);
      var edk := Mat.EncryptedDataKey(key_namespace, provider_info, edk_ctxt.value);
      x.plaintextDataKey := data_key;
      x.encryptedDataKeys := x.encryptedDataKeys + [edk];
      return Success(x);
    }

    function method ParseProviderInfo(info: seq<uint8>): Option<seq<uint8>> // returns the IV in the provider info, if it's of the right shape and key name is good
    {
      if |info| != |key_name| + 4 + 4 + 12 then None else
      if info[0..|key_name|] != key_name then None else
      Some(info[|key_name| + 8 ..])
    }

    method OnDecrypt(x: Mat.DecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.DecryptionMaterials>)
      requires Valid() 
      //requires x.Valid() //TODO Uncomment when valid is defined.
      modifies x`plaintextDataKey
      ensures Valid()
      //ensures res.Success? ==> res.value.Valid()
      ensures res.Success? ==> res.value == x
      ensures res.Failure? ==> unchanged(x)
    {
      if |edks| == 0 { return Failure("No edks given to OnDecrypt!"); }
      if edks[0].providerID != key_namespace { var res := OnDecrypt(x, edks[1..]); return res;}
      match ParseProviderInfo(edks[0].providerInfo) {
        case None => {var res := OnDecrypt(x, edks[1..]); return res;}
        case Some(iv) => {
          var flatEncCtx: seq<uint8> := if x.encryptionContext.Some?
                                        then Mat.FlattenSortEncCtx(x.encryptionContext.get)
                                        else []; //FIXME this is a hack, and I hate it.
          var octxt: Result<seq<uint8>> := AES.AES.aes_decrypt(aes_type, TAG_LEN, wrapping_key, edks[0].ciphertext, iv, flatEncCtx);
          match octxt {
            case Failure(e) => {var res := OnDecrypt(x, edks[1..]); return res;}
            case Success(ptKey) => {
              if |ptKey| == AlgorithmSuite.InputKeyLength(x.algorithmSuiteID) { // check for correct key length
                x.plaintextDataKey := Some(ptKey);
                return Success(x);
              }
              else {
                return Failure("Bad key length!");
              }
            }
          }
        }
      }
    }
  }
}
