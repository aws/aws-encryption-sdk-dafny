include "../MessageHeader/Definitions.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/GenBytes.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"

module AESKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Cipher
  import GenBytes = RNG
  import KeyringDefs
  import AESEncryption
  import Mat = Materials

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;

  class AESKeyring extends KeyringDefs.Keyring {
    const keyNamespace: string
    const keyName: string
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: Cipher.CipherParams

    predicate Valid() reads this {
        Repr == {this} &&
        (|wrappingKey| == Cipher.KeyLengthOfCipher(wrappingAlgorithm)) &&
        (wrappingAlgorithm in {Cipher.AES_GCM_128, Cipher.AES_GCM_192, Cipher.AES_GCM_256}) &&
        StringIs8Bit(keyNamespace) && StringIs8Bit(keyName)
    }

    constructor(namespace: string, name: string, key: seq<uint8>, wrappingAlg: Cipher.CipherParams)
    requires StringIs8Bit(namespace) && StringIs8Bit(name)
    requires wrappingAlg in {Cipher.AES_GCM_128, Cipher.AES_GCM_192, Cipher.AES_GCM_256}
    requires |key| == Cipher.KeyLengthOfCipher(wrappingAlg)
    ensures keyNamespace == namespace
    ensures keyName == name
    ensures wrappingKey == key
    ensures wrappingAlgorithm == wrappingAlg
    ensures Valid()
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      wrappingAlgorithm := wrappingAlg;
      Repr := {this};
    }

    function method SerializeProviderInto(iv: seq<uint8>): seq<uint8>
      requires Valid()
      requires |iv| == wrappingAlgorithm.ivLen as int
      reads this
    {
      StringToByteSeq(keyName) +
        [0, 0, 0, wrappingAlgorithm.tagLen * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLen] + // IV length in bytes
        iv
    }

    method OnEncrypt(encMat: Mat.EncryptionMaterials) returns (res: Result<Mat.EncryptionMaterials>)
      requires encMat.Valid()
      requires Valid()
      modifies encMat`plaintextDataKey
      modifies encMat`encryptedDataKeys
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Failure? ==> unchanged(encMat)
    {
      var dataKey := encMat.plaintextDataKey;
      if dataKey.None? {
        var k := Cipher.RNG.GenBytes(encMat.algorithmSuiteID.KeyLength() as uint16);
        dataKey := Some(k);
      }
      var iv := Cipher.RNG.GenBytes(wrappingAlgorithm.ivLen as uint16);
      var aad := Mat.FlattenSortEncCtx(encMat.encryptionContext);
      var encryptResult := AESEncryption.AES.aes_encrypt(wrappingAlgorithm, iv, wrappingKey, dataKey.get, aad);
      if encryptResult.Failure? { return Failure("Error on encrypt!"); }
      var providerInfo := SerializeProviderInto(iv);
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptResult.value);
      encMat.plaintextDataKey := dataKey;
      encMat.encryptedDataKeys := encMat.encryptedDataKeys + [edk];
      return Success(encMat);
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      ByteSeqToString(info[0..|keyName|]) == keyName &&
      SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }

    method OnDecrypt(decMat: Mat.DecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.DecryptionMaterials>)
      requires Valid() 
      requires decMat.Valid()
      modifies decMat`plaintextDataKey
      ensures Valid()
      ensures decMat.Valid()
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
    {
      if decMat.plaintextDataKey.Some? {
        return Success(decMat);
      }
      var i := 0;
      while i < |edks| {
        if edks[i].providerID == keyNamespace && ValidProviderInfo(edks[i].providerInfo) {
          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var flatEncCtx: seq<uint8> := Mat.FlattenSortEncCtx(decMat.encryptionContext);
          var decryptResult := AESEncryption.AES.aes_decrypt(wrappingAlgorithm, wrappingKey, edks[i].ciphertext, iv, flatEncCtx);
          if decryptResult.Success? {
            var ptKey := decryptResult.value;
            if |ptKey| == decMat.algorithmSuiteID.KeyLength() { // check for correct key length
              decMat.plaintextDataKey := Some(ptKey);
              return Success(decMat);
            }
          } else {
            return Failure("Decryption failed");
          }
        }
        i := i + 1;
      }
      return Success(decMat);
    }
  }
}
