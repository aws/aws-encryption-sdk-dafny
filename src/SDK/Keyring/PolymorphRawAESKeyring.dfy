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
include "../../Generated/AwsCryptographicMaterialProviders.dfy"

module {:extern "PolymorphRawAESKeyringDef"} PolymorphRawAESKeyringDef {
  import opened StandardLibrary
  import opened Wrappers
  import Aws.Crypto
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

  class PolymorphRawAESKeyring extends Crypto.IKeyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: EncryptionSuites.EncryptionSuite

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //= type=exception
    //# The wrapping key MUST be a secret value consisting of
    //# cryptographically secure pseudo-random bytes.

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //= type=exception
    //# It MUST be randomly
    //# generated from a cryptographically secure entropy source.

    predicate method Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && |wrappingKey| == wrappingAlgorithm.keyLen as int
      && wrappingAlgorithm in VALID_ALGORITHMS
      && wrappingAlgorithm.Valid()
      && |keyNamespace| < UINT16_LIMIT
    }

    // TODO move to materials
    predicate method ValidEncryptionMaterials(mat: Crypto.EncryptionMaterials) {
      && (AlgorithmSuite.PolymorphIDToInternalID(mat.algorithmSuiteID).SignatureType().Some? ==> mat.signingKey.Some?)
      && (mat.plaintextDataKey.Some? ==> AlgorithmSuite.PolymorphIDToInternalID(mat.algorithmSuiteID).ValidPlaintextDataKey(mat.plaintextDataKey.value))
      && (mat.plaintextDataKey.None? ==> |mat.encryptedDataKeys| == 0)
    }

    //= compliance/framework/raw-aes-keyring.txt#2.5
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, key: seq<uint8>, wrappingAlg: EncryptionSuites.EncryptionSuite)
      requires |namespace| < UINT16_LIMIT
      requires wrappingAlg in VALID_ALGORITHMS
      requires wrappingAlg.Valid()

      //= compliance/framework/raw-aes-keyring.txt#2.5.1
      //= type=implication
      //# The length
      //# of the wrapping key MUST be 128, 192, or 256.
      // TODO what does a condition like this mean for the shim?
      requires |key| == 16 || |key| == 24 || |key| == 32
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

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=implication
    //# OnEncrypt MUST take encryption materials (structures.md#encryption-
    //# materials) as input.
    method OnEncrypt(input: Crypto.OnEncryptInput) returns (res: Result<Crypto.OnEncryptOutput, string>)

      // Keyring Trait conditions
      // requires Valid()
      ensures res.Success? ==>
        && input.materials.encryptionContext == res.value.materials.encryptionContext
        && input.materials.algorithmSuiteID == res.value.materials.algorithmSuiteID
        && (input.materials.plaintextDataKey.Some? ==> res.value.materials.plaintextDataKey == input.materials.plaintextDataKey)
        && input.materials.encryptedDataKeys <= res.value.materials.encryptedDataKeys
        && input.materials.signingKey == res.value.materials.signingKey

      // EDK created using expected AAD
      ensures res.Success? ==>
        && var encCtxSerializable := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(input.materials.encryptionContext));
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && encCtxSerializable
        && wrappingAlgorithm.tagLen as nat <= |res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext|
        && var encOutput := DeserializeEDKCiphertext(res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext, wrappingAlgorithm.tagLen as nat);
        && AESEncryption.EncryptionOutputEncryptedWithAAD(encOutput, EncryptionContext.MapToSeq(input.materials.encryptionContext))

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //= type=implication
      //# Based on the ciphertext output of the AES-GCM decryption, the keyring
      //# MUST construct an encrypted data key (structures.md#encrypted-data-
      //# key) with the following specifics:
      ensures res.Success? ==>
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        // *  The key provider ID (structures.md#key-provider-id) is this
        // keyring's key namespace (./keyring-interface.md#key-namespace).
        && res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].providerID == keyNamespace
        // *  The key provider information (structures.md#key-provider-
        //   information) is serialized as the raw AES keyring key provider
        //   information (Section 2.6.1).
        && ValidProviderInfo(res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].providerInfo)
        // *  The ciphertext (structures.md#ciphertext) is serialized as the raw
        // AES keyring ciphertext (Section 2.6.2).
        // TODO ??? strongly tiw output to SerializeEDKCiphertext
        // TODO seperate these in spec?

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //= type=implication
      //# If the keyring cannot serialize
      //# the encryption context, OnEncrypt MUST fail.
      ensures !EncryptionContext.Serializable(input.materials.encryptionContext) ==> res.Failure?
    {
      // TODO missing ValidMaterials checks
      expect Valid();
      expect ValidEncryptionMaterials(input.materials);
      // Check that the encryption context can be serialized correctly
      reveal EncryptionContext.Serializable();
      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST attempt to serialize the encryption materials'
      //# (structures.md#encryption-materials) encryption context
      //# (structures.md#encryption-context-1) in the same format as the
      //# serialization of message header AAD key value pairs (../data-format/
      //# message-header.md#key-value-pairs).
      var valid := EncryptionContext.CheckSerializable(input.materials.encryptionContext);
      if !valid {
        return Failure("Unable to serialize encryption context");
      }

      var materialsWithDataKey := input.materials;
      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# If the encryption materials (structures.md#encryption-materials) do
      //# not contain a plaintext data key, OnEncrypt MUST generate a random
      //# plaintext data key and set it on the encryption materials
      //# (structures.md#encryption-materials).
      if materialsWithDataKey.plaintextDataKey.None? {
        var k :- Random.GenerateBytes(AlgorithmSuite.PolymorphIDToInternalID(input.materials.algorithmSuiteID).KeyLength() as int32);
        materialsWithDataKey := Crypto.EncryptionMaterials(
          encryptionContext := materialsWithDataKey.encryptionContext,
          algorithmSuiteID := materialsWithDataKey.algorithmSuiteID,
          signingKey := materialsWithDataKey.signingKey,
          plaintextDataKey := Some(k),
          encryptedDataKeys := []);
      }

      var iv :- Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var providerInfo := SerializeProviderInfo(iv);

      var wr := new Streams.ByteWriter();
      var _ :- Serialize.SerializeKVPairs(wr, input.materials.encryptionContext);
      var aad := wr.GetDataWritten();
      assert aad == EncryptionContext.MapToSeq(input.materials.encryptionContext);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST encrypt the plaintext data key in the encryption
      //# materials (structures.md#encryption-materials) using AES-GCM.
      var encryptResult :- AESEncryption.AESEncrypt(wrappingAlgorithm, iv, wrappingKey, materialsWithDataKey.plaintextDataKey.value, aad);
      var encryptedKey := SerializeEDKCiphertext(encryptResult);

      if UINT16_LIMIT <= |providerInfo| {
        return Failure("Serialized provider info too long.");
      }
      if UINT16_LIMIT <= |encryptedKey| {
        return Failure("Encrypted data key too long.");
      }
      var edk:Crypto.ValidEncryptedDataKey := Crypto.EncryptedDataKey(providerID := keyNamespace, providerInfo := providerInfo, ciphertext := encryptedKey);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST append the constructed encrypted data key to the
      //# encrypted data key list in the encryption materials
      //# (structures.md#encryption-materials).

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# OnEncrypt MUST output the modified encryption materials
      //# (structures.md#encryption-materials).
      var edks:seq<Crypto.ValidEncryptedDataKey> := materialsWithDataKey.encryptedDataKeys + [edk];
      var r := Crypto.EncryptionMaterials(
        encryptionContext := materialsWithDataKey.encryptionContext,
        algorithmSuiteID := materialsWithDataKey.algorithmSuiteID,
        signingKey := materialsWithDataKey.signingKey,
        plaintextDataKey := materialsWithDataKey.plaintextDataKey,
        encryptedDataKeys := edks);
      assert materialsWithDataKey.encryptedDataKeys == input.materials.encryptedDataKeys;
      assert |edks| == |materialsWithDataKey.encryptedDataKeys| + 1;
      assert r.encryptedDataKeys == edks;
      assert |r.encryptedDataKeys| == |edks|;
      assert |r.encryptedDataKeys| >= |input.materials.encryptedDataKeys|;
      res := Success(Crypto.OnEncryptOutput(materials := r));
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=implication
    //# OnDecrypt MUST take decryption input.materials (structures.md#decryption-
    //# input.materials) and a list of encrypted data keys
    //# (structures.md#encrypted-data-key) as input.
    method OnDecrypt(input: Crypto.OnDecryptInput) returns (res: Result<Crypto.OnDecryptOutput, string>)
      // Keyring Trait conditions
      // requires Valid()
      ensures Valid()
      ensures |input.encryptedDataKeys| == 0 ==> res.Success? && input.materials == res.value.materials
      ensures input.materials.plaintextDataKey.Some? ==> res.Success? && input.materials == res.value.materials
      ensures res.Success? ==>
          && input.materials.encryptionContext == res.value.materials.encryptionContext
          && input.materials.algorithmSuiteID == res.value.materials.algorithmSuiteID
          && (input.materials.plaintextDataKey.Some? ==> res.value.materials.plaintextDataKey == input.materials.plaintextDataKey)
          && res.value.materials.verificationKey == input.materials.verificationKey

      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=TODO
      //# If the decryption input.materials already contain a plaintext data key, the
      //# keyring MUST fail and MUST NOT modify the decryption input.materials
      //# (structures.md#decryption-input.materials).
      // We don't do this. We just pass through...

      // TODO: ensure non-None when input edk list has edk with valid provider info

      // Plaintext decrypted using expected AAD
      ensures res.Success? && input.materials.plaintextDataKey.None? && res.value.materials.plaintextDataKey.Some? ==>
        var encCtxSerializable := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(input.materials.encryptionContext));
        && encCtxSerializable
        && AESEncryption.PlaintextDecryptedWithAAD(res.value.materials.plaintextDataKey.value, EncryptionContext.MapToSeq(input.materials.encryptionContext))

      // If attempts to decrypt an EDK and the input EC cannot be serialized, return a Failure
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=implication
      //# If the keyring cannot
      //# serialize the encryption context, OnDecrypt MUST fail.
      ensures input.materials.plaintextDataKey.None? && !EncryptionContext.Serializable(input.materials.encryptionContext) && (exists i :: 0 <= i < |input.encryptedDataKeys| && ShouldDecryptEDK(input.encryptedDataKeys[i])) ==> res.Failure?
    {
      // TODO missing ValidMaterials checks
      expect Valid();

      if input.materials.plaintextDataKey.Some? {
        return Success(Crypto.OnDecryptOutput(materials:=input.materials));
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# The keyring MUST perform the following actions on each encrypted data
      //# key (structures.md#encrypted-data-key) in the input encrypted data
      //# key list, serially, until it successfully decrypts one.
      var i := 0;
      while i < |input.encryptedDataKeys|
        invariant forall prevIndex :: 0 <= prevIndex < i ==> prevIndex < |input.encryptedDataKeys| && !(ShouldDecryptEDK(input.encryptedDataKeys[prevIndex]))
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# The keyring MUST attempt to serialize the decryption input.materials'
          //# (structures.md#decryption-input.materials) encryption context
          //# (structures.md#encryption-context-1) in the same format as the
          //# serialization of the message header AAD key value pairs (../data-
          //# format/message-header.md#key-value-pairs).
          reveal EncryptionContext.Serializable();
          var valid := EncryptionContext.CheckSerializable(input.materials.encryptionContext);
          if !valid {
            return Failure("Unable to serialize encryption context");
          }
          var wr := new Streams.ByteWriter();
          var _ :- Serialize.SerializeKVPairs(wr, input.materials.encryptionContext);

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# For each encrypted data key (structures.md#encrypted-data-key), the
          //# keyring MUST first attempt to deserialize the serialized ciphertext
          //# (Section 2.6.2) to obtain the encrypted key (Section 2.6.2.1) and
          //# authentication tag (Section 2.6.2.2), and deserialize the serialized
          //# key provider info (Section 2.6.1) to obtain the key name (./keyring-
          //# interface.md#key-name), Section 2.6.1.4, IV length (Section 2.6.1.3),
          //# and authentication tag length (Section 2.6.1.2).
          // TODO without mocking there isn't a good way to test this...
          var aad := wr.GetDataWritten();
          assert aad == EncryptionContext.MapToSeq(input.materials.encryptionContext);
          var iv := GetIvFromProvInfo(input.encryptedDataKeys[i].providerInfo);
          var encryptionOutput := DeserializeEDKCiphertext(input.encryptedDataKeys[i].ciphertext, wrappingAlgorithm.tagLen as nat);

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If decrypting, the keyring MUST use AES-GCM with the following
          //# specifics:
          // TODO break up in spec
          var ptKey :- AESEncryption.AESDecrypt(wrappingAlgorithm, wrappingKey, encryptionOutput.cipherText, encryptionOutput.authTag, iv, aad);

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If a decryption succeeds, this keyring MUST add the resulting
          //# plaintext data key to the decryption input.materials and return the
          //# modified input.materials.
          if AlgorithmSuite.PolymorphIDToInternalID(input.materials.algorithmSuiteID).ValidPlaintextDataKey(ptKey) { // check for correct key length
            var r := Crypto.DecryptionMaterials(
            encryptionContext := input.materials.encryptionContext,
            algorithmSuiteID := input.materials.algorithmSuiteID,
            verificationKey := input.materials.verificationKey,
            plaintextDataKey := Some(ptKey));
            return Success(Crypto.OnDecryptOutput(materials:=r));
          } else {
            // TODO will this ever happen?
            return Failure("Decryption failed: bad datakey length.");
          }
        }
        i := i + 1;
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=TODO
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      // Right now we do the opposite, we always "succeed" does the spec need to change? How does this interoperate?
      return Success(Crypto.OnDecryptOutput(materials:=input.materials));
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //# The keyring MUST attempt to decrypt the encrypted data key if and
    //# only if the following is true:
    // TODO break up
    predicate method ShouldDecryptEDK(edk: Crypto.EncryptedDataKey) {
      edk.providerID == keyNamespace && ValidProviderInfo(edk.providerInfo) && wrappingAlgorithm.tagLen as int <= |edk.ciphertext|
    }

    // TODO #68: prove providerInfo serializes/deserializes correctly
    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      info[0..|keyName|] == keyName &&
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.2
      //= type=implication
      //# This value MUST be 128.
      SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == 128 &&
      SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32 &&
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.3
      //= type=implication
      //# This value MUST be 12.
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == 12
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }
  }
}
