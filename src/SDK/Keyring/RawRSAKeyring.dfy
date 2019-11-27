include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../../Util/UTF8.dfy"

module RawRSAKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KeyringDefs
  import AlgorithmSuite
  import RSA = RSAEncryption
  import Materials
  import Random
  import UTF8

  class RawRSAKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const paddingMode: RSA.RSAPaddingMode
    const bitLength: RSA.RSABitLength
    const encryptionKey: Option<seq<uint8>>
    const decryptionKey: Option<seq<uint8>>

    predicate Valid()
      reads this
    {
      Repr == {this} &&
      (encryptionKey.Some? ==> RSA.RSA.RSAWfEK(bitLength, paddingMode, encryptionKey.get)) &&
      (decryptionKey.Some? ==> RSA.RSA.RSAWfDK(bitLength, paddingMode, decryptionKey.get)) &&
      (encryptionKey.Some? || decryptionKey.Some?) &&
      |keyNamespace| < UINT16_LIMIT &&
      |keyName| < UINT16_LIMIT
    }

    constructor(namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, padding: RSA.RSAPaddingMode, bits: RSA.RSABitLength, ek: Option<seq<uint8>>, dk: Option<seq<uint8>>)
      requires ek.Some? ==> RSA.RSA.RSAWfEK(bits, padding, ek.get)
      requires dk.Some? ==> RSA.RSA.RSAWfDK(bits, padding, dk.get)
      requires ek.Some? || dk.Some?
      requires |namespace| < UINT16_LIMIT && |name| < UINT16_LIMIT
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures paddingMode == padding && bitLength == bits
      ensures encryptionKey == ek
      ensures decryptionKey == dk
      ensures Valid()
    {
      keyNamespace := namespace;
      keyName := name;
      paddingMode, bitLength := padding, bits;
      encryptionKey := ek;
      decryptionKey := dk;
      Repr := {this};
    }

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>) returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures res.Success? && res.value.Some? ==> 
        algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
        plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==>
        var generateTraces := Filter(res.value.get.keyringTrace, Materials.IsGenerateTrace);
        |generateTraces| == if plaintextDataKey.None? then 1 else 0
    {
      if encryptionKey.None? {
        return Failure("Encryption key undefined");
      } else {
        var plaintextDataKey := plaintextDataKey;
        var algorithmID := algorithmSuiteID;
        var keyringTrace := [];
        if plaintextDataKey.None? {
          var k := Random.GenerateBytes(algorithmID.KDFInputKeyLength() as int32);
          plaintextDataKey := Some(k);
          var generateTrace := Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.GENERATED_DATA_KEY});
          keyringTrace := keyringTrace + [generateTrace];
        }
        var aad := Materials.FlattenSortEncCtx(encryptionContext);
        var edkCiphertext := RSA.RSA.RSAEncrypt(bitLength, paddingMode, encryptionKey.get, plaintextDataKey.get);
        if edkCiphertext.None? {
          return Failure("Error on encrypt!");
        } else if UINT16_LIMIT <= |edkCiphertext.get| {
          return Failure("Encrypted data key too long.");
        }
        var edk := Materials.EncryptedDataKey(keyNamespace, keyName, edkCiphertext.get);
        
        var encryptTrace := Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.ENCRYPTED_DATA_KEY, Materials.SIGNED_ENCRYPTION_CONTEXT});
        FilterIsDistributive(keyringTrace, [encryptTrace], Materials.IsGenerateTrace);
        FilterIsDistributive(keyringTrace, [encryptTrace], Materials.IsEncryptTrace);
        keyringTrace := keyringTrace + [encryptTrace];
        
        var dataKey := Materials.DataKeyMaterials(algorithmSuiteID, plaintextDataKey.get, [edk], keyringTrace);
        assert dataKey.algorithmSuiteID.ValidPlaintextDataKey(dataKey.plaintextDataKey);
        return Success(Some(dataKey));
      }
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, 
                     encryptionContext: Materials.EncryptionContext, 
                     edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Option<KeyringDefs.ValidOnDecryptResult>>)
      requires Valid() 
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
    {
      if |edks| == 0 {
        return Success(None);
      } else if decryptionKey.None? {
        return Failure("Decryption key undefined");
      }
      var i := 0;
      while i < |edks|
        invariant  0 <= i <= |edks|
      {
        var edk := edks[i];
        if edk.providerID != keyNamespace {
          // continue with the next EDK
        } else if edk.providerInfo != keyName {
          // continue with the next EDK
        } else {
          var octxt := RSA.RSA.RSADecrypt(bitLength, paddingMode, decryptionKey.get, edks[0].ciphertext);
          match octxt
          case None =>
            // continue with the next EDK
          case Some(k) =>
            if algorithmSuiteID.ValidPlaintextDataKey(k) { // check for correct key length
              var decryptTrace := Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.DECRYPTED_DATA_KEY, Materials.VERIFIED_ENCRYPTION_CONTEXT});
              return Success(Some(KeyringDefs.OnDecryptResult(algorithmSuiteID, k, [decryptTrace])));
            } else {
              return Failure(("Bad key length!"));
            }
        }
        i := i + 1;
      }
      return Success(None);
    }
  }
}
