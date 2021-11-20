// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../AlgorithmSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"
include "../../Util/Streams.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"


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
  import Seq

  type WrappingAlgorithmSuiteId = id: Crypto.AlgorithmSuiteId |
    || id == Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
    || id == Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF
    || id == Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF
  witness *

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;

  class RawAESKeyring
    extends Keyring.VerifiableInterface
  {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes

    // The wrappingKey MUST be kept secret.
    // This is why storing this kind of wrapping key
    // in an key management system or HSM
    // is preferred.
    // The ESDK can not make such claims
    // on user supplied import.
    // Suffice to say: If these are not preserved
    // then the RawAESKeyring is not secure.

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //# The wrapping key MUST be a secret value consisting of
    //# cryptographically secure pseudo-random bytes.

    //= compliance/framework/raw-aes-keyring.txt#2.5.1
    //# It MUST be randomly
    //# generated from a cryptographically secure entropy source.
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: AESEncryption.AES_GCM



    //= compliance/framework/raw-aes-keyring.txt#2.5
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,
      key: seq<uint8>,
      wrappingAlgorithm: AESEncryption.AES_GCM
    )
      requires |namespace| < UINT16_LIMIT

      //= compliance/framework/raw-aes-keyring.txt#2.5.1
      //= type=implication
      //# The length
      //# of the wrapping key MUST be 128, 192, or 256.
      // TODO what does a condition like this mean for the shim?
      requires |key| == 16 || |key| == 24 || |key| == 32
      requires |key| == wrappingAlgorithm.keyLength as int
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures this.wrappingAlgorithm == wrappingAlgorithm
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      this.wrappingAlgorithm := wrappingAlgorithm;
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
        && EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && wrappingAlgorithm.tagLength as nat <= |res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext|
        && var encOutput := DeserializeEDKCiphertext(
          res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext,
          wrappingAlgorithm.tagLength as nat);
        && AESEncryption.EncryptionOutputEncryptedWithAAD(
          encOutput,
          EncryptionContextToAAD(input.materials.encryptionContext).value)

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
      ensures EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> res.Failure?
    {
      var materials := input.materials;
      var suite := GetSuite(materials.algorithmSuiteId);
      var aad :- EncryptionContextToAAD(materials.encryptionContext);

      // Random is a method, and transitions require both a key and encrypted data key
      var k' :- Random.GenerateBytes(suite.encrypt.keyLength as int32);
      var iv :- Random.GenerateBytes(wrappingAlgorithm.ivLength as int32);
      var providerInfo := SerializeProviderInfo(iv);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# If the encryption materials (structures.md#encryption-materials) do
      //# not contain a plaintext data key, OnEncrypt MUST generate a random
      //# plaintext data key and set it on the encryption materials
      //# (structures.md#encryption-materials).
      var plaintextDataKey := if materials.plaintextDataKey.None? then
        k'
      else
        materials.plaintextDataKey.value;

      :- Need(|wrappingKey|== wrappingAlgorithm.keyLength as int, "");
      :- Need(|iv| == wrappingAlgorithm.ivLength as int, "");

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST encrypt the plaintext data key in the encryption
      //# materials (structures.md#encryption-materials) using AES-GCM.
      var encryptResult :- AESEncryption.AESEncrypt(
        wrappingAlgorithm,
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

       // Plaintext decrypted using expected AAD
      ensures
        && res.Success?
        && input.materials.plaintextDataKey.None?
        && res.value.materials.plaintextDataKey.Some?
      ==>
        && EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && AESEncryption.PlaintextDecryptedWithAAD(
          res.value.materials.plaintextDataKey.value,
          EncryptionContextToAAD(input.materials.encryptionContext).value)

      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=implication
      //# If the keyring cannot
      //# serialize the encryption context, OnDecrypt MUST fail.
      ensures EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> res.Failure?
    {
      var materials := input.materials;
      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials), 
        "Keyring received decryption materials that already contain a plaintext data key.");

      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# The keyring MUST perform the following actions on each encrypted data
      //# key (structures.md#encrypted-data-key) in the input encrypted data
      //# key list, serially, until it successfully decrypts one.
      var i := 0;
      while i < |input.encryptedDataKeys|
        invariant forall prevIndex :: 0 <= prevIndex < i ==> prevIndex < |input.encryptedDataKeys| && !(ShouldDecryptEDK(input.encryptedDataKeys[prevIndex]))
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          var aad :- EncryptionContextToAAD(input.materials.encryptionContext);
          var iv := GetIvFromProvInfo(input.encryptedDataKeys[i].keyProviderInfo);
          var encryptionOutput := DeserializeEDKCiphertext(input.encryptedDataKeys[i].ciphertext, wrappingAlgorithm.tagLength as nat);

          :- Need(|wrappingKey|== wrappingAlgorithm.keyLength as int, "");
          :- Need(|iv| == wrappingAlgorithm.ivLength as int, "");

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If decrypting, the keyring MUST use AES-GCM with the following
          //# specifics:
          // TODO break up in spec
          var ptKey :- AESEncryption.AESDecrypt(
            wrappingAlgorithm,
            wrappingKey,
            encryptionOutput.cipherText,
            encryptionOutput.authTag,
            iv,
            aad
          );

          :- Need(GetSuite(materials.algorithmSuiteId).encrypt.keyLength as int == |ptKey|, "Decryption failed: bad datakey length.");

          //= compliance/framework/raw-aes-keyring.txt#2.7.2
          //# If a decryption succeeds, this keyring MUST add the resulting
          //# plaintext data key to the decryption input.materials and return the
          //# modified input.materials.
          var r :- Materials.DecryptionMaterialsAddDataKey(materials, ptKey);
          return Success(Crypto.OnDecryptOutput(materials:=r));
        }
        i := i + 1;
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      return Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.");
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires |iv| == wrappingAlgorithm.ivLength as int
    {
        keyName +
        [0, 0, 0, wrappingAlgorithm.tagLength * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLength as uint8] + // IV length in bytes
        iv
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //# The keyring MUST attempt to decrypt the encrypted data key if and
    //# only if the following is true:
    // TODO break up
    predicate method ShouldDecryptEDK(edk: Crypto.EncryptedDataKey) {
      // The key provider ID of the encrypted data key has a value equal to this keyring's key namespace.
      && edk.keyProviderId == keyNamespace
      && ValidProviderInfo(edk.keyProviderInfo)
      && wrappingAlgorithm.tagLength as int <= |edk.ciphertext|
    }

    // TODO #68: prove providerInfo serializes/deserializes correctly
    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      && |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLength as int
      // The key name obtained from the encrypted data key's key provider information has a value equal to this keyring's key name.
      && info[0..|keyName|] == keyName
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.2
      //= type=implication
      //# This value MUST be 128.
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == 128
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLength as uint32 * 8
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLength as uint32
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

  //= compliance/framework/raw-aes-keyring.txt#2.7.1
  //# The keyring MUST attempt to serialize the encryption materials'
  //# (structures.md#encryption-materials) encryption context
  //# (structures.md#encryption-context-1) in the same format as the
  //# serialization of message header AAD key value pairs (../data-format/
  //# message-header.md#key-value-pairs).
  function method EncryptionContextToAAD(
    encryptionContext: Crypto.EncryptionContext
  ): 
    (res: Result<seq<uint8>, string>)
  {
    :- Need(|encryptionContext| < UINT16_LIMIT, "Encryption Context is too large");
    var keys := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);

    var KeyIntoPairBytes := k
      requires k in encryptionContext
    =>
      var v := encryptionContext[k];
      :- Need(HasUint16Len(k) && HasUint16Len(v), "Unable to serialize encryption context");
      Success(UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);

    var pairsBytes :- Seq.MapWithResult(KeyIntoPairBytes, keys);

    Success(Seq.Flatten(pairsBytes))
  }

}
