// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../AlgorithmSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../../Crypto/EncryptionSuites.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"
include "../../Util/Streams.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"

// This dependency on the ESDK needs to be removed
// The ESDK depends on the AwsCryptographicMaterialProviders
// not the ohter way round.
include "../../SDK/EncryptionContext.dfy"
include "../../Util/Streams.dfy"
include "../../SDK/Serialize.dfy"

module
  {:extern "Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient2.RawAESKeyring"}
  AwsCryptographicMaterialProvidersClient2.RawAESKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import Aws.Crypto
  import AwsCryptographicMaterialProviders2.Keyring
  import AwsCryptographicMaterialProviders2.Materials
  import opened AwsCryptographicMaterialProviders2.AlgorithmSuites
  import opened UInt = StandardLibrary.UInt
  import Random
  import AESEncryption
  import UTF8

  // This dependency on the ESDK needs to be removed
  import EncryptionSuites
  import EncryptionContext
  import Streams
  import Serialize

  type WrappingAlgorithmSuiteId = id: Crypto.AlgorithmSuiteId |
    || id == Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
    || id == Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF
    || id == Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF
  witness *

  type WrappingAlgorithmSuite = suite: AlgorithmSuite |
    || suite == ALG_AES_128_GCM_IV12_TAG16_NO_KDF
    || suite == ALG_AES_192_GCM_IV12_TAG16_NO_KDF
    || suite == ALG_AES_256_GCM_IV12_TAG16_NO_KDF
  witness *

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;

  class RawAESKeyring
    extends Keyring.VerifiableInterface
  {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: WrappingAlgorithmSuite

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //= type=exception
    //# The wrapping key MUST be a secret value consisting of
    //# cryptographically secure pseudo-random bytes.

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //= type=exception
    //# It MUST be randomly
    //# generated from a cryptographically secure entropy source.

    //= compliance/framework/raw-aes-keyring.txt#2.5
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,
      key: seq<uint8>,
      wrappingAlgId: WrappingAlgorithmSuiteId
    )
      requires |namespace| < UINT16_LIMIT

      //= compliance/framework/raw-aes-keyring.txt#2.5.1
      //= type=implication
      //# The length
      //# of the wrapping key MUST be 128, 192, or 256.
      // TODO what does a condition like this mean for the shim?
      requires |key| == 16 || |key| == 24 || |key| == 32
      requires |key| == GetSuite(wrappingAlgId).keyLen as int
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures wrappingAlgorithm == GetSuite(wrappingAlgId)
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      wrappingAlgorithm := GetSuite(wrappingAlgId);
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=implication
    //# OnEncrypt MUST take encryption materials (structures.md#encryption-
    //# materials) as input.
    method OnEncrypt(input: Crypto.OnEncryptInput)
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

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
        && res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].keyProviderId == keyNamespace
        // *  The key provider information (structures.md#key-provider-
        //   information) is serialized as the raw AES keyring key provider
        //   information (Section 2.6.1).
        && ValidProviderInfo(res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].keyProviderInfo)
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
      // Check that the encryption context can be serialized correctly
      reveal EncryptionContext.Serializable();
      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST attempt to serialize the encryption materials'
      //# (structures.md#encryption-materials) encryption context
      //# (structures.md#encryption-context-1) in the same format as the
      //# serialization of message header AAD key value pairs (../data-format/
      //# message-header.md#key-value-pairs).
      var valid := EncryptionContext.CheckSerializable(input.materials.encryptionContext);
      :- Need(valid, "Unable to serialize encryption context");

      var materials := input.materials;
      var suite := GetSuite(materials.algorithmSuiteId);

      // Random is a method, and transitions require both a key and encrypted data key
      var k' :- Random.GenerateBytes(suite.keyLen as int32);
      var iv :- Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var providerInfo := SerializeProviderInfo(iv);

      var wr := new Streams.ByteWriter();
      var _ :- Serialize.SerializeKVPairs(wr, input.materials.encryptionContext);
      var aad := wr.GetDataWritten();
      assert aad == EncryptionContext.MapToSeq(input.materials.encryptionContext);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# If the encryption materials (structures.md#encryption-materials) do
      //# not contain a plaintext data key, OnEncrypt MUST generate a random
      //# plaintext data key and set it on the encryption materials
      //# (structures.md#encryption-materials).
      var plaintextDataKey := if materials.plaintextDataKey.None? then
        k'
      else
        materials.plaintextDataKey.value;

      var encAlg :- EncryptionSuites.Translate(wrappingAlgorithm);
      :- Need(|wrappingKey|== encAlg.keyLen as int, "");
      :- Need(|iv| == encAlg.ivLen as int, "");

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST encrypt the plaintext data key in the encryption
      //# materials (structures.md#encryption-materials) using AES-GCM.
      var encryptResult :- AESEncryption.AESEncrypt(
        encAlg,
        iv,
        wrappingKey,
        plaintextDataKey,
        aad
      );
      var encryptedKey := SerializeEDKCiphertext(encryptResult);

      :- Need(HasUint16Len(providerInfo), "Serialized provider info too long.");
      :- Need(HasUint16Len(encryptedKey), "Encrypted data key too long.");
      var edk:Crypto.EncryptedDataKey := Crypto.EncryptedDataKey(keyProviderId := keyNamespace, keyProviderInfo := providerInfo, ciphertext := encryptedKey);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST append the constructed encrypted data key to the
      //# encrypted data key list in the encryption materials
      //# (structures.md#encryption-materials).

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# OnEncrypt MUST output the modified encryption materials
      //# (structures.md#encryption-materials).

      var r :- if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk])
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
      return Success(Crypto.OnEncryptOutput(materials := r));
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=implication
    //# OnDecrypt MUST take decryption input.materials (structures.md#decryption-
    //# input.materials) and a list of encrypted data keys
    //# (structures.md#encrypted-data-key) as input.
    method OnDecrypt(input: Crypto.OnDecryptInput)

      returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )
      // TODO: ensure non-None when input edk list has edk with valid provider info

      // // Plaintext decrypted using expected AAD
      ensures res.Success? && input.materials.plaintextDataKey.None? && res.value.materials.plaintextDataKey.Some? ==>
        var encCtxSerializable := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(input.materials.encryptionContext));
        && encCtxSerializable
        && AESEncryption.PlaintextDecryptedWithAAD(res.value.materials.plaintextDataKey.value, EncryptionContext.MapToSeq(input.materials.encryptionContext))

      // // If attempts to decrypt an EDK and the input EC cannot be serialized, return a Failure
      // //= compliance/framework/raw-aes-keyring.txt#2.7.2
      // //= type=implication
      // //# If the keyring cannot
      // //# serialize the encryption context, OnDecrypt MUST fail.
      ensures input.materials.plaintextDataKey.None? && !EncryptionContext.Serializable(input.materials.encryptionContext) && (exists i :: 0 <= i < |input.encryptedDataKeys| && ShouldDecryptEDK(input.encryptedDataKeys[i])) ==> res.Failure?
    {
      var materials := input.materials;
      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials), 
        "Keyring recieved decryption materials that already contain a plaintext data key.");

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
          var valid := EncryptionContext.CheckSerializable(materials.encryptionContext);
          if !valid {
            return Failure("Unable to serialize encryption context");
          }
          var wr := new Streams.ByteWriter();
          var _ :- Serialize.SerializeKVPairs(wr, materials.encryptionContext);

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
          assert aad == EncryptionContext.MapToSeq(materials.encryptionContext);
          var iv := GetIvFromProvInfo(input.encryptedDataKeys[i].keyProviderInfo);
          var encryptionOutput := DeserializeEDKCiphertext(input.encryptedDataKeys[i].ciphertext, wrappingAlgorithm.tagLen as nat);

          var encAlg :- EncryptionSuites.Translate(wrappingAlgorithm);
          :- Need(|wrappingKey|== encAlg.keyLen as int, "");
          :- Need(|iv| == encAlg.ivLen as int, "");

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If decrypting, the keyring MUST use AES-GCM with the following
          //# specifics:
          // TODO break up in spec
          var ptKey :- AESEncryption.AESDecrypt(
            encAlg,
            wrappingKey,
            encryptionOutput.cipherText,
            encryptionOutput.authTag,
            iv,
            aad
          );

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If a decryption succeeds, this keyring MUST add the resulting
          //# plaintext data key to the decryption input.materials and return the
          //# modified input.materials.
          :- Need(GetSuite(materials.algorithmSuiteId).keyLen as int == |ptKey|, "Decryption failed: bad datakey length.");

          var r :- Materials.DecryptionMaterialsAddDataKey(materials, ptKey);
          return Success(Crypto.OnDecryptOutput(materials:=r));
        }
        i := i + 1;
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=TODO
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      return Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.");
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires |iv| == wrappingAlgorithm.ivLen as int
    {
        keyName +
        [0, 0, 0, wrappingAlgorithm.tagLen * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLen as uint8] + // IV length in bytes
        iv
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //# The keyring MUST attempt to decrypt the encrypted data key if and
    //# only if the following is true:
    // TODO break up
    predicate method ShouldDecryptEDK(edk: Crypto.EncryptedDataKey) {
      && edk.keyProviderId == keyNamespace
      && ValidProviderInfo(edk.keyProviderInfo)
      && wrappingAlgorithm.tagLen as int <= |edk.ciphertext|
    }

    // TODO #68: prove providerInfo serializes/deserializes correctly
    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      && |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int
      && info[0..|keyName|] == keyName
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.2
      //= type=implication
      //# This value MUST be 128.
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == 128
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.3
      //= type=implication
      //# This value MUST be 12.
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == 12
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }
  }

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

}
