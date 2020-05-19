// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../AlgorithmSuite.dfy"
include "./Defs.dfy"
include "../../Crypto/EncryptionSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"
include "../MessageHeader.dfy"
include "../EncryptionContext.dfy"
include "../Serialize.dfy"
include "../../Util/UTF8.dfy"
include "../../Util/Streams.dfy"

module {:extern "RawAESKeyringDef"} RawAESKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import EncryptionSuites
  import AlgorithmSuite
  import Random
  import KeyringDefs
  import AESEncryption
  import Mat = Materials
  import MessageHeader
  import UTF8
  import EncryptionContext
  import Serialize
  import Streams

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;
  const VALID_ALGORITHMS := {EncryptionSuites.AES_GCM_128, EncryptionSuites.AES_GCM_192, EncryptionSuites.AES_GCM_256}

  function method DeserializeEDKCiphertext(ciphertext: seq<uint8>, tagLen: nat): (encOutput: AESEncryption.EncryptionOutput)
    requires tagLen <= |ciphertext|
    ensures |encOutput.authTag| == tagLen
  {
      var encryptedKeyLength := |ciphertext| - tagLen as int;
      AESEncryption.EncryptionOutput(ciphertext[.. encryptedKeyLength], ciphertext[encryptedKeyLength ..])
  }

  function method SerializeEDKCiphertext(encOutput: AESEncryption.EncryptionOutput): (ciphertext: seq<uint8>) {
    encOutput.cipherText + encOutput.authTag
  }

  lemma EDKSerializeDeserialize(encOutput: AESEncryption.EncryptionOutput)
    ensures DeserializeEDKCiphertext(SerializeEDKCiphertext(encOutput), |encOutput.authTag|) == encOutput
  {}

  lemma EDKDeserializeSerialze(ciphertext: seq<uint8>, tagLen: nat)
    requires tagLen <= |ciphertext|
    ensures SerializeEDKCiphertext(DeserializeEDKCiphertext(ciphertext, tagLen)) == ciphertext
  {}

  class RawAESKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: EncryptionSuites.EncryptionSuite

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && |wrappingKey| == wrappingAlgorithm.keyLen as int
      && wrappingAlgorithm in VALID_ALGORITHMS
      && wrappingAlgorithm.Valid()
      && |keyNamespace| < UINT16_LIMIT
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, key: seq<uint8>, wrappingAlg: EncryptionSuites.EncryptionSuite)
      requires |namespace| < UINT16_LIMIT
      requires wrappingAlg in VALID_ALGORITHMS
      requires wrappingAlg.Valid()
      requires |key| == wrappingAlg.keyLen as int
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures wrappingAlgorithm == wrappingAlg
      ensures Valid() && fresh(Repr)
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
      reads Repr
    {
        keyName +
        [0, 0, 0, wrappingAlgorithm.tagLen * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLen] + // IV length in bytes
        iv
    }

    method OnEncrypt(materials: Mat.ValidEncryptionMaterials) returns (res: Result<Mat.ValidEncryptionMaterials>)
      // Keyring Trait conditions
      requires Valid()
      ensures res.Success? ==>
        && materials.encryptionContext == res.value.encryptionContext
        && materials.algorithmSuiteID == res.value.algorithmSuiteID
        && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
        && materials.keyringTrace <= res.value.keyringTrace
        && materials.encryptedDataKeys <= res.value.encryptedDataKeys
        && materials.signingKey == res.value.signingKey

      // EDK created using expected AAD
      ensures res.Success? ==>
        && var encCtxSerializable := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(materials.encryptionContext));
        && |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1
        && encCtxSerializable
        && wrappingAlgorithm.tagLen as nat <= |res.value.encryptedDataKeys[|materials.encryptedDataKeys|].ciphertext|
        && var encOutput := DeserializeEDKCiphertext(res.value.encryptedDataKeys[|materials.encryptedDataKeys|].ciphertext, wrappingAlgorithm.tagLen as nat);
        && AESEncryption.EncryptionOutputEncryptedWithAAD(encOutput, EncryptionContext.MapToSeq(materials.encryptionContext))

      // EDK created has expected providerID and valid providerInfo
      ensures res.Success? ==>
        && |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1
        && res.value.encryptedDataKeys[|materials.encryptedDataKeys|].providerID == keyNamespace
        && ValidProviderInfo(res.value.encryptedDataKeys[|materials.encryptedDataKeys|].providerInfo)

      // KeyringTrace generated as expected
      ensures res.Success? ==>
        && if materials.plaintextDataKey.None? then
          && |res.value.keyringTrace| == |materials.keyringTrace| + 2
          && res.value.keyringTrace[|materials.keyringTrace|] == GenerateTraceEntry()
          && res.value.keyringTrace[|materials.keyringTrace| + 1] == EncryptTraceEntry()
        else
          && |res.value.keyringTrace| == |materials.keyringTrace| + 1
          && res.value.keyringTrace[|materials.keyringTrace|] == EncryptTraceEntry()

      // If input EC cannot be serialized, returns a Failure
      ensures !EncryptionContext.Serializable(materials.encryptionContext) ==> res.Failure?
    {
      // Check that the encryption context can be serialized correctly
      reveal EncryptionContext.Serializable();
      var valid := EncryptionContext.CheckSerializable(materials.encryptionContext);
      if !valid {
        return Failure("Unable to serialize encryption context");
      }

      var materialsWithDataKey := materials;
      if materialsWithDataKey.plaintextDataKey.None? {
        var k :- Random.GenerateBytes(materials.algorithmSuiteID.KeyLength() as int32);
        materialsWithDataKey := materialsWithDataKey.WithKeys(Some(k), [], [GenerateTraceEntry()]);
      }

      var iv :- Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var providerInfo := SerializeProviderInfo(iv);

      var wr := new Streams.ByteWriter();
      var _ :- Serialize.SerializeKVPairs(wr, materials.encryptionContext);
      var aad := wr.GetDataWritten();
      assert aad == EncryptionContext.MapToSeq(materials.encryptionContext);

      var encryptResult :- AESEncryption.AESEncrypt(wrappingAlgorithm, iv, wrappingKey, materialsWithDataKey.plaintextDataKey.get, aad);
      var encryptedKey := SerializeEDKCiphertext(encryptResult);

      if UINT16_LIMIT <= |providerInfo| {
        return Failure("Serialized provider info too long.");
      }
      if UINT16_LIMIT <= |encryptedKey| {
        return Failure("Encrypted data key too long.");
      }
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptedKey);

      var encryptTraceEntry := EncryptTraceEntry();
      FilterIsDistributive(materialsWithDataKey.keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
      res := Success(materialsWithDataKey.WithKeys(materialsWithDataKey.plaintextDataKey, [edk], [encryptTraceEntry]));
    }

    method OnDecrypt(materials: Mat.ValidDecryptionMaterials,
                     edks: seq<Mat.EncryptedDataKey>) returns (res: Result<Mat.ValidDecryptionMaterials>)
      // Keyring Trait conditions
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && res.value.verificationKey == materials.verificationKey

      // TODO: ensure non-None when input edk list has edk with valid provider info

      // Plaintext decrypted using expected AAD
      ensures res.Success? && materials.plaintextDataKey.None? && res.value.plaintextDataKey.Some? ==>
        var encCtxSerializable := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(materials.encryptionContext));
        && encCtxSerializable
        && AESEncryption.PlaintextDecryptedWithAAD(res.value.plaintextDataKey.get, EncryptionContext.MapToSeq(materials.encryptionContext))

      // KeyringTrace generated as expected
      ensures res.Success? && materials.plaintextDataKey.None? && res.value.plaintextDataKey.Some? ==>
          |res.value.keyringTrace| == |materials.keyringTrace| + 1 && res.value.keyringTrace[|materials.keyringTrace|] == DecryptTraceEntry()

      // If attempts to decrypt an EDK and the input EC cannot be serialized, return a Failure
      ensures materials.plaintextDataKey.None? && !EncryptionContext.Serializable(materials.encryptionContext) && (exists i :: 0 <= i < |edks| && ShouldDecryptEDK(edks[i])) ==> res.Failure?
    {
      if materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      var i := 0;
      while i < |edks|
        invariant forall prevIndex :: 0 <= prevIndex < i ==> prevIndex < |edks| && !(ShouldDecryptEDK(edks[prevIndex]))
      {
        if ShouldDecryptEDK(edks[i]) {
          // Check that the encryption context can be serialized correctly
          reveal EncryptionContext.Serializable();
          var valid := EncryptionContext.CheckSerializable(materials.encryptionContext);
          if !valid {
            return Failure("Unable to serialize encryption context");
          }
          var wr := new Streams.ByteWriter();
          var _ :- Serialize.SerializeKVPairs(wr, materials.encryptionContext);
          var aad := wr.GetDataWritten();
          assert aad == EncryptionContext.MapToSeq(materials.encryptionContext);

          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var encryptionOutput := DeserializeEDKCiphertext(edks[i].ciphertext, wrappingAlgorithm.tagLen as nat);
          var ptKey :- AESEncryption.AESDecrypt(wrappingAlgorithm, wrappingKey, encryptionOutput.cipherText, encryptionOutput.authTag, iv, aad);

          var decryptTraceEntry := DecryptTraceEntry();
          if materials.algorithmSuiteID.ValidPlaintextDataKey(ptKey) { // check for correct key length
            return Success(materials.WithPlaintextDataKey(ptKey, [decryptTraceEntry]));
          } else {
            return Failure("Decryption failed: bad datakey length.");
          }
        }
        i := i + 1;
      }
      return Success(materials);
    }

    predicate method ShouldDecryptEDK(edk: Mat.EncryptedDataKey) {
      edk.providerID == keyNamespace && ValidProviderInfo(edk.providerInfo) && wrappingAlgorithm.tagLen as int <= |edk.ciphertext|
    }

    // TODO #68: prove providerInfo serializes/deserializes correctly
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
