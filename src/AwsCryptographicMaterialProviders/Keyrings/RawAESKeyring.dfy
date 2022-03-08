// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/String.dfy"
include "../AlgorithmSuites.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/AESEncryption.dfy"
include "../Materials.dfy"
include "../../Util/UTF8.dfy"
include "../../Util/Streams.dfy"
include "../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.RawAESKeyring"}
  MaterialProviders.RawAESKeyring
{
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened String = StandardLibrary.String
  import opened Wrappers
  import Aws.Crypto
  import Keyring
  import Materials
  import opened AlgorithmSuites
  import Random
  import AESEncryption
  import UTF8
  import Seq

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;

  class RawAESKeyring
    extends
    Keyring.VerifiableInterface,
    Crypto.IKeyring
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
      returns (res: Result<Crypto.OnEncryptOutput, Crypto.IAwsCryptographicMaterialProvidersClientException>)
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
      var aadResult := EncryptionContextToAAD(materials.encryptionContext);
      var aad :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(aadResult);

      // Random is a method, and transitions require both a key and encrypted data key
      var randomKeyResult := Random.GenerateBytes(suite.encrypt.keyLength as int32);
      var k' :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(randomKeyResult);
      var randomIvResult := Random.GenerateBytes(wrappingAlgorithm.ivLength as int32);
      var iv :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(randomIvResult);
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

      :- Crypto.Need(|wrappingKey|== wrappingAlgorithm.keyLength as int,
        "Wrapping key length does not match algorithm");
      :- Crypto.Need(|iv| == wrappingAlgorithm.ivLength as int,
        "IV length does not match algorithm");

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST encrypt the plaintext data key in the encryption
      //# materials (structures.md#encryption-materials) using AES-GCM.
      var aesEncryptResult := AESEncryption.AESEncrypt(
        wrappingAlgorithm,
        iv,
        wrappingKey,
        plaintextDataKey,
        aad
      );
      var encryptResult :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(aesEncryptResult);
      var encryptedKey := SerializeEDKCiphertext(encryptResult);

      :- Crypto.Need(HasUint16Len(providerInfo),
        "Serialized provider info too long.");
      :- Crypto.Need(HasUint16Len(encryptedKey),
        "Encrypted data key too long.");

      var edk: Crypto.EncryptedDataKey := Crypto.EncryptedDataKey(keyProviderId := keyNamespace, keyProviderInfo := providerInfo, ciphertext := encryptedKey);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST append the constructed encrypted data key to the
      //# encrypted data key list in the encryption materials
      //# (structures.md#encryption-materials).

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# OnEncrypt MUST output the modified encryption materials
      //# (structures.md#encryption-materials).
      var addKeyResult := if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk])
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
      var r :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(addKeyResult);
      return Success(Crypto.OnEncryptOutput(materials := r));
    }

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=implication
    //# OnDecrypt MUST take decryption materials (structures.md#decryption-
    //# materials) and a list of encrypted data keys
    //# (structures.md#encrypted-data-key) as input.
    method OnDecrypt(input: Crypto.OnDecryptInput)
      returns (res: Result<Crypto.OnDecryptOutput, Crypto.IAwsCryptographicMaterialProvidersClientException>)
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
      :- Crypto.Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        "Keyring received decryption materials that already contain a plaintext data key.");

      var aadResult := EncryptionContextToAAD(input.materials.encryptionContext);
      var aad :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(aadResult);
      :- Crypto.Need(|wrappingKey|== wrappingAlgorithm.keyLength as int,
        "The wrapping key does not match the wrapping algorithm");

      var errors: seq<string> := [];
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# The keyring MUST perform the following actions on each encrypted data
      //# key (structures.md#encrypted-data-key) in the input encrypted data
      //# key list, serially, until it successfully decrypts one.
      for i := 0 to |input.encryptedDataKeys|
        invariant |errors| == i
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {

          var iv := GetIvFromProvInfo(input.encryptedDataKeys[i].keyProviderInfo);
          var encryptionOutput := DeserializeEDKCiphertext(
            input.encryptedDataKeys[i].ciphertext,
            wrappingAlgorithm.tagLength as nat
          );

          var ptKeyRes := this.Decrypt(iv, encryptionOutput, input.materials.encryptionContext);
          if ptKeyRes.Success?
          {
            :- Crypto.Need(
              GetSuite(materials.algorithmSuiteId).encrypt.keyLength as int == |ptKeyRes.Extract()|,
              // this should never happen
              "Plaintext Data Key is not the expected length");
            //= compliance/framework/raw-aes-keyring.txt#2.7.2
            //# If a decryption succeeds, this keyring MUST add the resulting
            //# plaintext data key to the decryption materials and return the
            //# modified materials.
            var addKeyResult := Materials.DecryptionMaterialsAddDataKey(materials, ptKeyRes.Extract());
            var r :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(addKeyResult);
            return Success(Crypto.OnDecryptOutput(materials := r));
          } else {
            errors := errors + [
              "AESKeyring could not decrypt EncryptedDataKey "
              + Base10Int2String(i)
              + ": "
              + ptKeyRes.error
            ];
          }
        } else {
          errors := errors + [
            "EncrypedDataKey "
            + Base10Int2String(i)
            + " did not match AESKeyring. "
          ];
        }
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      var combinedErrorsException := new Crypto.AwsCryptographicMaterialProvidersClientException(
        "Unable to decrypt any data keys. Encountered the following errors: " + Seq.Flatten(errors));
      return Failure(combinedErrorsException);
    }

    //TODO This needs to be a private method
    method Decrypt(
      iv: seq<uint8>,
      encryptionOutput: AESEncryption.EncryptionOutput,
      encryptionContext: Crypto.EncryptionContext
    ) returns (res: Result<seq<uint8>, string>)
      requires |encryptionOutput.authTag| == wrappingAlgorithm.tagLength as int
      requires |wrappingKey| == wrappingAlgorithm.keyLength as int
      ensures
        res.Success?
      ==>
        && EncryptionContextToAAD(encryptionContext).Success?
        && AESEncryption.PlaintextDecryptedWithAAD(
          res.value,
          EncryptionContextToAAD(encryptionContext).value
        )
    {
      :- Need(|iv| == wrappingAlgorithm.ivLength as int, "");
      var aad :- EncryptionContextToAAD(encryptionContext);
      var ptKey: seq<uint8> :- AESEncryption.AESDecrypt(
        wrappingAlgorithm,
        wrappingKey,
        encryptionOutput.cipherText,
        encryptionOutput.authTag,
        iv,
        aad
      );
      return Success(ptKey);
    }


    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires |iv| == wrappingAlgorithm.ivLength as int
    {
        keyName +
        [0, 0, 0, wrappingAlgorithm.tagLength * 8] + // tag length in bits
        [0, 0, 0, wrappingAlgorithm.ivLength as uint8] + // IV length in bytes
        iv
    }

    // TODO bring in the broken up spec statements
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
      //# This value MUST match the authentication tag length of the keyring's
      //# configured wrapping algorithm

      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == 128
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLength as uint32 * 8
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLength as uint32
      //= compliance/framework/raw-aes-keyring.txt#2.6.1.3
      //= type=implication
      //# This value MUST match the IV length of the keyring's
      //# configured wrapping algorithm
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == 12
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN ..]
    }
  }

  function method DeserializeEDKCiphertext(
    ciphertext: seq<uint8>,
    tagLen: nat
  ): ( encOutput: AESEncryption.EncryptionOutput)
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
  // TODO: Tests/proofs
  function method EncryptionContextToAAD(
    encryptionContext: Crypto.EncryptionContext
  ):
    (res: Result<seq<uint8>, string>)
  {
    :- Need(|encryptionContext| < UINT16_LIMIT, "Encryption Context is too large");
    var keys := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);

    if |keys| == 0 then
      // TODO: this adheres to spec (message-header.md) but diverges from what we do
      // in EncryptionContext.WriteAADSection
      Success([])
    else
      var KeyIntoPairBytes := k
        requires k in encryptionContext
      =>
        var v := encryptionContext[k];
        :- Need(HasUint16Len(k) && HasUint16Len(v), "Unable to serialize encryption context");
        Success(UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);

      var pairsBytes :- Seq.MapWithResult(KeyIntoPairBytes, keys);

      // The final return should be the bytes of the pairs, prepended with the number of pairs
      var allBytes := UInt16ToSeq(|keys| as uint16) + Seq.Flatten(pairsBytes);
      Success(allBytes)
  }

}
