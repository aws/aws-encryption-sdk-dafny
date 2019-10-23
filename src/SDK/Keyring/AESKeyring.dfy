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

    method SerializeProviderInto(iv: seq<uint8>) returns (res: seq<uint8>)
      requires Valid()
      requires |iv| == wrappingAlgorithm.ivLen as int
      ensures ValidProviderInfo(res)
    {
      res := StringToByteSeq(keyName) +
        [0, 0, 0, wrappingAlgorithm.tagLen * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLen] + // IV length in bytes
        iv;
      
      StringByteSeqCorrect(keyName);
      assert res[0..|keyName|] == StringToByteSeq(keyName);
    }

    method OnEncrypt(encMat: Mat.EncryptionMaterials) returns (res: Result<Mat.EncryptionMaterials>)
      /* Keyring trait specification */
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys, encMat`keyringTrace
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Failure? ==> unchanged(encMat)
      ensures old(encMat.plaintextDataKey.Some?) ==> unchanged(encMat`plaintextDataKey)
      ensures old(encMat.encryptedDataKeys) <= encMat.encryptedDataKeys
      ensures old(encMat.keyringTrace) <= encMat.keyringTrace
      
      /* Raw AES Keyring specification */
      // If added an EDK, the EDK providerID and providerInfo was set correctly for this keyring
      ensures |encMat.encryptedDataKeys| > |old(encMat.encryptedDataKeys)| ==>
        var newEDK := encMat.encryptedDataKeys[|encMat.encryptedDataKeys| - 1];
        newEDK.providerID == keyNamespace &&
        ValidProviderInfo(newEDK.providerInfo)
      // Iff added an EDK but did not set the plaintextDataKey, the appropriate trace is also added
      ensures |encMat.encryptedDataKeys| > |old(encMat.encryptedDataKeys)| && old(encMat.plaintextDataKey).Some? <==> (
        |encMat.keyringTrace| == |old(encMat.keyringTrace)| + 1 &&
        var encryptTrace := encMat.keyringTrace[|encMat.keyringTrace| - 1];
        encryptTrace.flags == {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT} &&
        encryptTrace.keyNamespace == keyNamespace &&
        encryptTrace.keyName == keyName
      )
      // Iff set the plaintextDataKey and added an EDK, the appropriate traces are also added
      ensures |encMat.encryptedDataKeys| > |old(encMat.encryptedDataKeys)| && old(encMat.plaintextDataKey).None? <==> (
        |encMat.keyringTrace| == |old(encMat.keyringTrace)| + 2 &&
        var encryptTrace := encMat.keyringTrace[|encMat.keyringTrace|-1];
        encryptTrace.flags == {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT} &&
        encryptTrace.keyNamespace == keyNamespace &&
        encryptTrace.keyName == keyName &&
        var generateTrace := encMat.keyringTrace[|encMat.keyringTrace|-2];
        generateTrace.flags == {Mat.GENERATED_DATA_KEY} &&
        generateTrace.keyNamespace == keyNamespace &&
        generateTrace.keyName == keyName
      )
    {
      var dataKey := encMat.plaintextDataKey;
      if dataKey.None? {
        var k := Random.GenerateBytes(encMat.algorithmSuiteID.KeyLength() as int32);
        dataKey := Some(k);
      }
      var iv := Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var aad := Mat.FlattenSortEncCtx(encMat.encryptionContext);
      var encryptResult := AESEncryption.AES.aes_encrypt(wrappingAlgorithm, iv, wrappingKey, dataKey.get, aad);
      if encryptResult.Failure? { 
        return Failure("Error on encrypt!");
      }

      if encMat.plaintextDataKey.None? {
        var generateTrace := Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.GENERATED_DATA_KEY});
        encMat.SetPlaintextDataKey(dataKey.get, generateTrace);
      }

      var providerInfo := SerializeProviderInto(iv);
      assert ValidProviderInfo(providerInfo);
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptResult.value);
      var encryptTrace := Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
      encMat.AppendEncryptedDataKey(edk, encryptTrace);
      
      return Success(encMat);
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      ByteSeqToString(info[0..|keyName|]) == keyName &&
      SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }

    method OnDecrypt(decMat: Mat.DecryptionMaterials, edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.DecryptionMaterials>)
      /* Keyring Trait specific */
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey, decMat`keyringTrace
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == decMat
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Failure? ==> unchanged(decMat)

      /* Raw AES Keyring specific */
      // Iff set a plaintextDataKey, the appropriate trace is also added
      ensures old(decMat.plaintextDataKey).None? && decMat.plaintextDataKey.Some? ==> (
        |decMat.keyringTrace| == |old(decMat.keyringTrace)| + 1 &&
        var decryptTrace := decMat.keyringTrace[|decMat.keyringTrace|-1];
        decryptTrace.flags == {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT} &&
        decryptTrace.keyNamespace == keyNamespace &&
        decryptTrace.keyName == keyName
      )
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
              var decryptTrace := Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT});
              decMat.SetPlaintextDataKey(ptKey, decryptTrace);
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
