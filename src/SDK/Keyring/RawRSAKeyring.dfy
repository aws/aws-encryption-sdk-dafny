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

  import AlgorithmSuite
  import KeyringDefs
  import Materials
  import Random
  import RSA = RSAEncryption
  import UTF8

  class RawRSAKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const paddingMode: RSA.RSAPaddingMode
    const publicKey: Option<seq<uint8>>
    const privateKey: Option<seq<uint8>>

    predicate Valid()
      reads this
    {
      Repr == {this} &&
      (publicKey.Some? || privateKey.Some?) &&
      (publicKey.Some? ==> RSA.RSA.RSAWfEK(paddingMode, publicKey.get)) &&
      (privateKey.Some? ==> RSA.RSA.RSAWfDK(paddingMode, privateKey.get)) &&
      |keyNamespace| < UINT16_LIMIT &&
      |keyName| < UINT16_LIMIT
    }

    constructor(namespace: UTF8.ValidUTF8Bytes,name: UTF8.ValidUTF8Bytes, padding: RSA.RSAPaddingMode,
                encryptionKey: Option<seq<uint8>>, decryptionKey: Option<seq<uint8>>)
      requires (encryptionKey.Some? || decryptionKey.Some?) &&
        (encryptionKey.Some? ==> RSA.RSA.RSAWfEK(padding, encryptionKey.get)) &&
        (decryptionKey.Some? ==> RSA.RSA.RSAWfDK(padding, decryptionKey.get))
      requires |namespace| < UINT16_LIMIT && |name| < UINT16_LIMIT
      ensures keyNamespace == namespace && keyName == name &&
        paddingMode == padding &&
        publicKey == encryptionKey && privateKey == decryptionKey
      ensures Valid()
    {
      keyNamespace, keyName := namespace, name;
      paddingMode := padding;
      publicKey, privateKey := encryptionKey, decryptionKey;
      Repr := {this};
    }

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID,
                     encryptionContext: Materials.EncryptionContext,
                     plaintextDataKey: Option<seq<uint8>>)
      returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      // NOTE: encryptionContext is intentionally unused
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==> 
        algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> 
        plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==>
        var generateTraces := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry);
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
      if publicKey.None? {
        return Failure("Encryption key undefined");
      } else {
        var plaintextDataKey := plaintextDataKey;
        var algorithmID := algorithmSuiteID;
        var keyringTrace := [];

        // If no plaintext data key exists, generate a random plaintext data key
        if plaintextDataKey.None? {
          var k := Random.GenerateBytes(algorithmID.KDFInputKeyLength() as int32);
          plaintextDataKey := Some(k);
          var generateTraceEntry := GenerateTraceEntry();
          keyringTrace := keyringTrace + [generateTraceEntry];
        }

        // Attempt to encrypt and construct the encrypted data key
        var encryptedCiphertext :- RSA.RSA.RSAEncrypt(paddingMode, publicKey.get, plaintextDataKey.get);
        if UINT16_LIMIT <= |encryptedCiphertext| {
          return Failure("Encrypted data key too long.");
        }
        var encryptedDataKey := Materials.EncryptedDataKey(keyNamespace, keyName, encryptedCiphertext);

        // Construct the necessary trace
        var encryptTraceEntry := EncryptTraceEntry();
        FilterIsDistributive(keyringTrace, [encryptTraceEntry], Materials.IsGenerateTraceEntry);
        FilterIsDistributive(keyringTrace, [encryptTraceEntry], Materials.IsEncryptTraceEntry);
        keyringTrace := keyringTrace + [encryptTraceEntry];
        
        // Finally return the dataKey
        var dataKey := Materials.DataKeyMaterials(algorithmID, plaintextDataKey.get, [encryptedDataKey], keyringTrace);
        assert dataKey.algorithmSuiteID.ValidPlaintextDataKey(dataKey.plaintextDataKey);
        return Success(Some(dataKey));
      }
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, 
                     encryptionContext: Materials.EncryptionContext, 
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>)
      returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      ensures res.Success? && res.value.Some? ==> |res.value.get.keyringTrace| == 1
        && res.value.get.keyringTrace[0] == DecryptTraceEntry()
    {
      if |encryptedDataKeys| == 0 {
        return Success(None);
      } else if privateKey.None? {
        return Failure("Decryption key undefined");
      }
      var i := 0;
      while i < |encryptedDataKeys|
        invariant  0 <= i <= |encryptedDataKeys|
      {
        var encryptedDataKey := encryptedDataKeys[i];
        if encryptedDataKey.providerID == keyNamespace && encryptedDataKey.providerInfo == keyName {
          var potentialPlaintextDataKey := RSA.RSA.RSADecrypt(paddingMode, privateKey.get, encryptedDataKey.ciphertext);
          match potentialPlaintextDataKey
          case Failure(_) =>
            // Try to decrypt using another encryptedDataKey
          case Success(plaintextDataKey) =>
            // Validate the key length before returning
            if algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
              var decryptTraceEntry := DecryptTraceEntry();
              return Success(Some(Materials.OnDecryptResult(algorithmSuiteID, plaintextDataKey, [decryptTraceEntry])));
            } else {
              return Failure("Bad key length!");
            }
        }
        i := i + 1;
      }
      return Success(None);
    }

    function method GenerateTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.GENERATED_DATA_KEY})
    }

    function method EncryptTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.ENCRYPTED_DATA_KEY})
    }

    function method DecryptTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.DECRYPTED_DATA_KEY})
    }
  }
}
