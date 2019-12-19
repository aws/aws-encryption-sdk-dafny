include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/EncryptionSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"

module RawAESKeyring{
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionSuites
  import AlgorithmSuite
  import Random
  import KeyringDefs
  import AESEncryption
  import Mat = Materials
  import UTF8

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;
  const VALID_ALGORITHMS := {EncryptionSuites.AES_GCM_128, EncryptionSuites.AES_GCM_192, EncryptionSuites.AES_GCM_256}

  class RawAESKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: EncryptionSuites.EncryptionSuite

    predicate Valid() reads this {
      && Repr == {this}
      && |wrappingKey| == wrappingAlgorithm.keyLen as int
      && wrappingAlgorithm in VALID_ALGORITHMS
      && wrappingAlgorithm.Valid()
      && |keyNamespace| < UINT16_LIMIT
    }

    constructor(namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, key: seq<uint8>, wrappingAlg: EncryptionSuites.EncryptionSuite)
      requires |namespace| < UINT16_LIMIT
      requires wrappingAlg in VALID_ALGORITHMS
      requires wrappingAlg.Valid()
      requires |key| == wrappingAlg.keyLen as int
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

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires Valid()
      requires |iv| == wrappingAlgorithm.ivLen as int
      reads this
    {
        keyName +
        [0, 0, 0, wrappingAlgorithm.tagLen * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLen] + // IV length in bytes
        iv
    }

    method OnEncrypt(algorithmSuiteID: Mat.AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Mat.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==>
        algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==>
        plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==>
        var generateTraces: seq<Mat.KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Mat.IsGenerateTraceEntry);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0
      ensures res.Success? && res.value.Some? ==>
        if plaintextDataKey.None? then
          && |res.value.get.keyringTrace| == 2
          && res.value.get.keyringTrace[0] == GenerateTraceEntry()
          && res.value.get.keyringTrace[1] == EncryptTraceEntry()
        else
          && |res.value.get.keyringTrace| == 1
          && res.value.get.keyringTrace[0] == EncryptTraceEntry()
    {
      var keyringTrace := [];
      var plaintextDataKey := plaintextDataKey;
      if plaintextDataKey.None? {
        var k := Random.GenerateBytes(algorithmSuiteID.KeyLength() as int32);
        plaintextDataKey := Some(k);
        var generateTraceEntry := GenerateTraceEntry();
        keyringTrace := keyringTrace + [generateTraceEntry];
      }

      var iv := Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var aad := Mat.FlattenSortEncCtx(encryptionContext);
      var encryptResult :- AESEncryption.AESEncrypt(wrappingAlgorithm, iv, wrappingKey, plaintextDataKey.get, aad);
      var encryptedKey := encryptResult.cipherText + encryptResult.authTag;
      var providerInfo := SerializeProviderInfo(iv);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure("Serialized provider info too long.");
      }
      if UINT16_LIMIT <= |encryptedKey| {
        return Failure("Encrypted data key too long.");
      }
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptedKey);

      var encryptTraceEntry := EncryptTraceEntry();
      FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
      FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsEncryptTraceEntry);
      keyringTrace := keyringTrace + [encryptTraceEntry];

      res := Success(Some(Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey.get, [edk], keyringTrace)));
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID,
                     encryptionContext: Mat.EncryptionContext,
                     edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Option<Mat.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      // TODO: ensure non-None when input edk list has edk with valid provider info
      ensures res.Success? && res.value.Some? ==> |res.value.get.keyringTrace| == 1 && res.value.get.keyringTrace[0] == DecryptTraceEntry()
    {
      var i := 0;
      while i < |edks|
      {
        if edks[i].providerID == keyNamespace && ValidProviderInfo(edks[i].providerInfo) && wrappingAlgorithm.tagLen as int <= |edks[i].ciphertext| {
          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var flatEncCtx: seq<uint8> := Mat.FlattenSortEncCtx(encryptionContext);
          //TODO: #68
          var encryptedKeyLength := |edks[i].ciphertext| - wrappingAlgorithm.tagLen as int;
          // TODO: specify Raw AES EDK ciphertext serialization
          var encryptedKey, authTag := edks[i].ciphertext[.. encryptedKeyLength], edks[i].ciphertext[encryptedKeyLength ..];
          var ptKey :- AESEncryption.AESDecrypt(wrappingAlgorithm, wrappingKey, encryptedKey, authTag, iv, flatEncCtx);
          var decryptTraceEntry := DecryptTraceEntry();
          if algorithmSuiteID.ValidPlaintextDataKey(ptKey) { // check for correct key length
            return Success(Some(Mat.OnDecryptResult(algorithmSuiteID, ptKey, [decryptTraceEntry])));
          } else {
            return Failure("Decryption failed: bad datakey length.");
          }
        }
        i := i + 1;
      }
      return Success(None);
    }

    // TODO prove providerInfo serializes/deserializes correctly
    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      info[0..|keyName|] == keyName &&
      SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }

    function method GenerateTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.GENERATED_DATA_KEY})
    }

    function method EncryptTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT})
    }

    function method DecryptTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT})
    }
  }
}
