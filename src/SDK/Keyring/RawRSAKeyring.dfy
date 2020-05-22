// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../../Util/UTF8.dfy"

module {:extern "RawRSAKeyringDef"} RawRSAKeyringDef {
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
    const paddingMode: RSA.PaddingMode
    const publicKey: Option<RSA.PublicKey>
    const privateKey: Option<RSA.PrivateKey>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      (publicKey.Some? || privateKey.Some?) &&
      (publicKey.Some? ==> ValidComponent(publicKey.get)) &&
      (publicKey.Some? ==> publicKey.get.padding == paddingMode) &&
      (privateKey.Some? ==> ValidComponent(privateKey.get)) &&
      (privateKey.Some? ==> privateKey.get.padding == paddingMode) &&
      |keyNamespace| < UINT16_LIMIT &&
      |keyName| < UINT16_LIMIT
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, padding: RSA.PaddingMode,
                 publicKey: Option<RSA.PublicKey>, privateKey: Option<RSA.PrivateKey>)
      requires publicKey.Some? || privateKey.Some?
      requires publicKey.Some? ==> publicKey.get.Valid()
      requires publicKey.Some? ==> publicKey.get.padding == padding
      requires privateKey.Some? ==> privateKey.get.Valid()
      requires privateKey.Some? ==> privateKey.get.padding == padding
      requires |namespace| < UINT16_LIMIT
      requires |name| < UINT16_LIMIT
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures paddingMode == padding
      ensures this.publicKey == publicKey
      ensures this.privateKey == privateKey
      ensures Valid() && fresh(Repr - KeyRepr(publicKey) - KeyRepr(privateKey))
    {
      keyNamespace, keyName := namespace, name;
      paddingMode := padding;
      this.publicKey := publicKey;
      this.privateKey := privateKey;
      Repr := {this} + KeyRepr(publicKey) + KeyRepr(privateKey);
    }

    static function KeyRepr(key: Option<RSA.Key>): set<object>
      reads if key.Some? then {key.get} else {}
    {
      if key.Some? then key.get.Repr else {}
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      // NOTE: encryptionContext is intentionally unused
      ensures publicKey.None? ==> res.Failure?
      ensures res.Success? ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
        && materials.keyringTrace <= res.value.keyringTrace
        && materials.encryptedDataKeys <= res.value.encryptedDataKeys
        && materials.signingKey == res.value.signingKey
      ensures res.Success? ==>
        (forall i :: |materials.encryptedDataKeys| <= i < |res.value.encryptedDataKeys| ==>
        res.value.encryptedDataKeys[i].providerID == keyNamespace && res.value.encryptedDataKeys[i].providerInfo == keyName)
      ensures res.Success? && materials.plaintextDataKey.None? && res.value.plaintextDataKey.Some? ==>
        var generateTraces: seq<Materials.KeyringTraceEntry> := Filter(res.value.keyringTrace, Materials.IsGenerateTraceEntry);
        |generateTraces| == if materials.plaintextDataKey.None? then 1 else 0
      ensures res.Success? ==>
        if materials.plaintextDataKey.None? then
          && |res.value.keyringTrace| == 2
          && res.value.keyringTrace[|materials.keyringTrace|] == GenerateTraceEntry()
          && res.value.keyringTrace[|materials.keyringTrace| + 1] == EncryptTraceEntry()
        else
          && |res.value.keyringTrace| == |materials.keyringTrace| + 1
          && res.value.keyringTrace[|materials.keyringTrace|] == EncryptTraceEntry()
    {
      if publicKey.None? {
        return Failure("Encryption key undefined");
      }

      // If no plaintext data key exists, generate a random plaintext data key
      var materialsWithDataKey := materials;
      if materials.plaintextDataKey.None? {
        var k :- Random.GenerateBytes(materialsWithDataKey.algorithmSuiteID.KDFInputKeyLength() as int32);
        materialsWithDataKey := materials.WithKeys(Some(k), [], [GenerateTraceEntry()]);
      }

      // Attempt to encrypt and construct the encrypted data key
      var encryptedCiphertext :- RSA.Encrypt(paddingMode, publicKey.get, materialsWithDataKey.plaintextDataKey.get);
      if UINT16_LIMIT <= |encryptedCiphertext| {
        return Failure("Encrypted data key too long.");
      }
      var encryptedDataKey := Materials.EncryptedDataKey(keyNamespace, keyName, encryptedCiphertext);

      // Construct the necessary trace
      var encryptTraceEntry := EncryptTraceEntry();
      FilterIsDistributive(materialsWithDataKey.keyringTrace, [encryptTraceEntry], Materials.IsGenerateTraceEntry);

      // Finally return the dataKey
      var materials := materialsWithDataKey.WithKeys(materialsWithDataKey.plaintextDataKey, [encryptedDataKey], [encryptTraceEntry]);
      assert materials.Valid();
      return Success(materials);
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
        && materials.keyringTrace <= res.value.keyringTrace
        && res.value.verificationKey == materials.verificationKey
      ensures privateKey.None? && materials.plaintextDataKey.None? && |encryptedDataKeys| > 0 ==> res.Failure?
      ensures res.Success? && materials.plaintextDataKey.None? && res.value.plaintextDataKey.Some? ==> |res.value.keyringTrace| == |materials.keyringTrace| + 1
        && res.value.keyringTrace[|materials.keyringTrace|] == DecryptTraceEntry()
    {
      if materials.plaintextDataKey.Some? || |encryptedDataKeys| == 0 {
        return Success(materials);
      } else if privateKey.None? {
        return Failure("Decryption key undefined");
      }
      var i := 0;
      while i < |encryptedDataKeys|
        invariant  0 <= i <= |encryptedDataKeys|
      {
        var encryptedDataKey := encryptedDataKeys[i];
        if encryptedDataKey.providerID == keyNamespace &&
          encryptedDataKey.providerInfo == keyName &&
          (0 < |encryptedDataKey.ciphertext|) {
          var potentialPlaintextDataKey := RSA.Decrypt(paddingMode, privateKey.get, encryptedDataKey.ciphertext);
          match potentialPlaintextDataKey
          case Failure(_) =>
            // Try to decrypt using another encryptedDataKey
          case Success(plaintextDataKey) =>
            // Validate the key length before returning
            if materials.algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
              var decryptTraceEntry := DecryptTraceEntry();
              return Success(materials.WithPlaintextDataKey(plaintextDataKey, [decryptTraceEntry]));
            } else {
              return Failure("Bad key length!");
            }
        }
        i := i + 1;
      }
      return Success(materials);
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
