include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/Cipher.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"

module AESKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite
  import Cipher
  import Random
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

    method OnEncrypt(encMat: Mat.ValidEncryptionMaterialsInput) returns (res: Result<Option<Mat.ValidDataKey>>)
      requires Valid()
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==> 
        encMat.algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? ==> 
        (encMat.plaintextDataKey.Some? ==> encMat.plaintextDataKey.get == res.value.get.plaintextDataKey)
    {
      var plaintextDataKey := encMat.plaintextDataKey;
      if plaintextDataKey.None? {
        var k := Random.GenerateBytes(encMat.algorithmSuiteID.KeyLength() as int32);
        plaintextDataKey := Some(k);
      }
      var iv := Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var aad := Mat.FlattenSortEncCtx(encMat.encryptionContext);
      var encryptResult := AESEncryption.AES.aes_encrypt(wrappingAlgorithm, iv, wrappingKey, plaintextDataKey.get, aad);
      if encryptResult.Failure? { return Failure("Error on encrypt!"); }
      var providerInfo := SerializeProviderInto(iv);
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptResult.value);
      var dataKey := Mat.DataKey(encMat.algorithmSuiteID, plaintextDataKey.get, [edk]);
      assert dataKey.algorithmSuiteID.ValidPlaintextDataKey(dataKey.plaintextDataKey);
      return Success(Some(dataKey));
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

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext, edks: seq<Mat.EncryptedDataKey>) 
      returns (res: Result<Option<Mat.DecryptionMaterialsOutput>>)
      requires Valid() 
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
    {
      var i := 0;
      while i < |edks| {
        if edks[i].providerID == keyNamespace && ValidProviderInfo(edks[i].providerInfo) {
          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var flatEncCtx: seq<uint8> := Mat.FlattenSortEncCtx(encryptionContext);
          var decryptResult := AESEncryption.AES.aes_decrypt(wrappingAlgorithm, wrappingKey, edks[i].ciphertext, iv, flatEncCtx);
          if decryptResult.Success? {
            var ptKey := decryptResult.value;
            if |ptKey| == algorithmSuiteID.KeyLength() { // check for correct key length
              var dataKey := Mat.DataKey(algorithmSuiteID, ptKey, edks);
              return Success(Some(Mat.DecryptionMaterialsOutput(dataKey, None)));
            }
          } else {
            return Failure("Decryption failed");
          }
        }
        i := i + 1;
      }
      return Success(None);
    }
  }
}
