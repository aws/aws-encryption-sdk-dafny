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
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Cipher
  import GenBytes = RNG
  import KeyringDefs
  import AESEncryption
  import Mat = Materials

  class AESKeyring extends KeyringDefs.Keyring {
    const keyNamespace: string
    const keyName: string
    const wrappingKey: seq<uint8>
    const aesType: Cipher.CipherParams

    predicate Valid() reads this {
        Repr == {this} &&
        (|wrappingKey| == Cipher.KeyLengthOfCipher(aesType)) &&
        (aesType in {Cipher.AES_GCM_128, Cipher.AES_GCM_192, Cipher.AES_GCM_256}) &&
        ValidUTF8(keyNamespace) && ValidUTF8(keyName)
    }

    constructor(namespace: string, name: string, key: seq<uint8>, params: Cipher.CipherParams)
    //TODO Verify that CipherParams contains valid values.
    requires ValidUTF8(namespace) && ValidUTF8(name)
    requires params in {Cipher.AES_GCM_128, Cipher.AES_GCM_192, Cipher.AES_GCM_256}
    requires |key| == Cipher.KeyLengthOfCipher(params)
    ensures keyNamespace == namespace
    ensures keyName == name
    ensures wrappingKey == key
    ensures aesType == params
    ensures Valid()
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      aesType := params;
      Repr := {this};
    }

    function method AESProviderInfo(iv: seq<uint8>): seq<uint8>
      requires Valid()
      requires |iv| == aesType.ivLen as int
      reads this
    {
      StringToByteSeq(keyName) + 
        [0, 0, 0, aesType.tagLen * 8] + // tag length in bits
        [0, 0, 0, aesType.ivLen] + // IV length in bytes
        iv
    }

    method OnEncrypt(encMat: Mat.EncryptionMaterials) returns (res: Result<Mat.EncryptionMaterials>)
      requires encMat.Valid()
      requires Valid() ensures Valid()
      modifies encMat`plaintextDataKey
      modifies encMat`encryptedDataKeys
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Failure? ==> unchanged(encMat)
    {
      var dataKey := encMat.plaintextDataKey;
      var algSuiteID := encMat.algorithmSuiteID;
      if dataKey.None? {
        var k := Cipher.RNG.GenBytes(AlgorithmSuite.InputKeyLength(algSuiteID) as uint16);
        dataKey := Some(k);
      }
      var iv := Cipher.RNG.GenBytes(aesType.ivLen as uint16);
      var aad := if encMat.encryptionContext.Some?
                 then Mat.FlattenSortEncCtx(encMat.encryptionContext.get)
                 else []; //FIXME this is a hack, and I hate it.
      var encryptResult := AESEncryption.AES.aes_encrypt(aesType, iv, wrappingKey, dataKey.get, aad);
      if encryptResult.Failure? { return Failure("Error on encrypt!"); }
      var providerInfo := AESProviderInfo(iv);
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptResult.value);
      encMat.plaintextDataKey := dataKey;
      encMat.encryptedDataKeys := encMat.encryptedDataKeys + [edk];
      return Success(encMat);
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      //TODO Replace 4s with descriptive constants for auth tag length length, and IV length length
      |info| == |keyName| + 4 + 4 + 12 &&
      ByteSeqToString(info[0..|keyName|]) == keyName &&
      seqToUInt32(info[|keyName|..|keyName| + 4]) == aesType.tagLen as uint32 &&
      seqToUInt32(info[|keyName| + 4 .. |keyName| + 4 + 4]) == aesType.ivLen as uint32
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + 8 ..]
    }

    method OnDecrypt(decMat: Mat.DecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.DecryptionMaterials>)
      requires Valid() 
      //requires x.Valid() //TODO Uncomment when valid is defined.
      modifies decMat`plaintextDataKey
      ensures Valid()
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? &&
                                                res.value == decMat &&
                                                unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
    {
      if decMat.plaintextDataKey.Some? {
        return Success(decMat);
      } else if |edks| == 0 {
        return Failure("No edks given to OnDecrypt!");
      }
      var i := |edks|;
      while i < |edks| {
        if edks[i].providerID == keyNamespace && ValidProviderInfo(edks[i].providerInfo) {
          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var flatEncCtx: seq<uint8> := if decMat.encryptionContext.Some?
                                        then Mat.FlattenSortEncCtx(decMat.encryptionContext.get)
                                        else []; //FIXME this is a hack, and I hate it.
          var decryptResult := AESEncryption.AES.aes_decrypt(aesType, Cipher.TAG_LEN, wrappingKey, edks[0].ciphertext, iv, flatEncCtx);
          if decryptResult.Success? {
            var ptKey := decryptResult.value;
            if |ptKey| == AlgorithmSuite.InputKeyLength(decMat.algorithmSuiteID) { // check for correct key length
              decMat.plaintextDataKey := Some(ptKey);
              return Success(decMat);
            }
          }
        }
      }
      return Failure("Could not decrypt with any given EDK");
    }
  }
}
