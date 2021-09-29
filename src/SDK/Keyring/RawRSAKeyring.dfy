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
  import opened Wrappers
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
      (publicKey.Some? ==>
        publicKey.value in Repr && publicKey.value.Repr <= Repr && this !in publicKey.value.Repr && publicKey.value.Valid()) &&
      (publicKey.Some? ==> publicKey.value.padding == paddingMode) &&
      (privateKey.Some? ==>
        privateKey.value in Repr && privateKey.value.Repr <= Repr && this !in privateKey.value.Repr && privateKey.value.Valid()) &&
      (privateKey.Some? ==> privateKey.value.padding == paddingMode) &&
      |keyNamespace| < UINT16_LIMIT &&
      |keyName| < UINT16_LIMIT
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, padding: RSA.PaddingMode,
                 publicKey: Option<RSA.PublicKey>, privateKey: Option<RSA.PrivateKey>)
      requires publicKey.Some? || privateKey.Some?
      requires publicKey.Some? ==> publicKey.value.Valid()
      requires publicKey.Some? ==> publicKey.value.padding == padding
      requires privateKey.Some? ==> privateKey.value.Valid()
      requires privateKey.Some? ==> privateKey.value.padding == padding
      requires |namespace| < UINT16_LIMIT
      requires |name| < UINT16_LIMIT
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures paddingMode == padding
      ensures this.publicKey == publicKey
      ensures this.privateKey == privateKey
      ensures Valid() && fresh(Repr - KeyRepr(publicKey) - KeyRepr(privateKey))
    {
      keyNamespace := namespace;
      keyName := name;
      paddingMode := padding;
      this.publicKey := publicKey;
      this.privateKey := privateKey;
      Repr := {this} + KeyRepr(publicKey) + KeyRepr(privateKey);
    }

    static function KeyRepr(key: Option<RSA.Key>): set<object>
      reads if key.Some? then {key.value} else {}
    {
      if key.Some? then key.value.Repr else {}
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      // NOTE: encryptionContext is intentionally unused
      ensures publicKey.None? ==> res.Failure?
      ensures res.Success? ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
        && materials.encryptedDataKeys <= res.value.encryptedDataKeys
        && materials.signingKey == res.value.signingKey
      ensures res.Success? ==>
        (forall i :: |materials.encryptedDataKeys| <= i < |res.value.encryptedDataKeys| ==>
        res.value.encryptedDataKeys[i].providerID == keyNamespace && res.value.encryptedDataKeys[i].providerInfo == keyName)
    {
      if publicKey.None? {
        return Failure("Encryption key undefined");
      }

      // If no plaintext data key exists, generate a random plaintext data key
      var materialsWithDataKey := materials;
      if materials.plaintextDataKey.None? {
        var k :- Random.GenerateBytes(materialsWithDataKey.algorithmSuiteID.KDFInputKeyLength() as int32);
        materialsWithDataKey := materials.WithKeys(Some(k), []);
      }

      // Attempt to encrypt and construct the encrypted data key
      var encryptedCiphertext :- RSA.Encrypt(paddingMode, publicKey.value, materialsWithDataKey.plaintextDataKey.value);
      if UINT16_LIMIT <= |encryptedCiphertext| {
        return Failure("Encrypted data key too long.");
      }
      var encryptedDataKey := Materials.EncryptedDataKey(keyNamespace, keyName, encryptedCiphertext);

      // Finally return the dataKey
      var materials := materialsWithDataKey.WithKeys(materialsWithDataKey.plaintextDataKey, [encryptedDataKey]);
      assert materials.Valid();
      return Success(materials);
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
        && res.value.verificationKey == materials.verificationKey
      ensures privateKey.None? && materials.plaintextDataKey.None? && |encryptedDataKeys| > 0 ==> res.Failure?
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
          var potentialPlaintextDataKey := RSA.Decrypt(paddingMode, privateKey.value, encryptedDataKey.ciphertext);
          match potentialPlaintextDataKey
          case Failure(_) =>
            // Try to decrypt using another encryptedDataKey
          case Success(plaintextDataKey) =>
            // Validate the key length before returning
            if materials.algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
              return Success(materials.WithPlaintextDataKey(plaintextDataKey));
            } else {
              return Failure("Bad key length!");
            }
        }
        i := i + 1;
      }
      return Success(materials);
    }
  }
}
