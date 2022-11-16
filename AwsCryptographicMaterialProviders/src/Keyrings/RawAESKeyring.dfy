// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../Materials.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module RawAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened String = StandardLibrary.String
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import Keyring
  import Materials
  import opened AlgorithmSuites
  import UTF8
  import Seq

  import Aws.Cryptography.Primitives

  const AUTH_TAG_LEN_LEN := 4;
  const IV_LEN_LEN       := 4;

  class RawAESKeyring
    extends
    Keyring.VerifiableInterface,
    Types.IKeyring
  {
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && cryptoPrimitives.Modifies <= Modifies
      && History !in cryptoPrimitives.Modifies
      && cryptoPrimitives.ValidState()
    }

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
    const wrappingAlgorithm: Crypto.AES_GCM

    //= compliance/framework/raw-aes-keyring.txt#2.5
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,
      key: seq<uint8>,
      wrappingAlgorithm: Crypto.AES_GCM,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires |namespace| < UINT16_LIMIT
      requires |name| < UINT16_LIMIT

      //= compliance/framework/raw-aes-keyring.txt#2.5.1
      //= type=implication
      //# The length
      //# of the wrapping key MUST be 128, 192, or 256.
      // TODO what does a condition like this mean for the shim?
      requires |key| == 16 || |key| == 24 || |key| == 32
      requires |key| == wrappingAlgorithm.keyLength as int
      requires cryptoPrimitives.ValidState()
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures this.wrappingAlgorithm == wrappingAlgorithm
      ensures this.cryptoPrimitives == cryptoPrimitives
      ensures ValidState() && fresh(History) && fresh(Modifies - cryptoPrimitives.Modifies)
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      this.wrappingAlgorithm := wrappingAlgorithm;
      this.cryptoPrimitives := cryptoPrimitives;

      History := new Types.IKeyringCallHistory();
      Modifies := { History } + cryptoPrimitives.Modifies;

    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>) {true}

    //= compliance/framework/raw-aes-keyring.txt#2.7.1
    //= type=implication
    //# OnEncrypt MUST take encryption materials (structures.md#encryption-
    //# materials) as input.
    method  OnEncrypt'(input: Types.OnEncryptInput)
      returns (output: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures output.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          output.value.materials
        )

      // EDK created using expected AAD
      ensures output.Success?
      ==>
        && EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && |cryptoPrimitives.History.GenerateRandomBytes| == |old(cryptoPrimitives.History.GenerateRandomBytes)| + 2
        && |cryptoPrimitives.History.AESEncrypt| == |old(cryptoPrimitives.History.AESEncrypt)| + 1
        && Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.Success?
        && Seq.Last(Seq.DropLast(cryptoPrimitives.History.GenerateRandomBytes)).output.Success?
        && Seq.Last(cryptoPrimitives.History.AESEncrypt).output.Success?
        && var iv :=  Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.value;
        && var AESEncryptInput := Seq.Last(cryptoPrimitives.History.AESEncrypt).input;
        && var AESEncryptOutput := Seq.Last(cryptoPrimitives.History.AESEncrypt).output.value;
        && AESEncryptInput.encAlg == wrappingAlgorithm
        && AESEncryptInput.key == wrappingKey
        && AESEncryptInput.iv == iv
        && AESEncryptInput.aad == EncryptionContextToAAD(input.materials.encryptionContext).value 
        && var edk := Seq.Last(output.value.materials.encryptedDataKeys);
        && edk.keyProviderId == keyNamespace
        && |iv| == wrappingAlgorithm.ivLength as int
        && edk.keyProviderInfo == SerializeProviderInfo(iv)
        && edk.ciphertext == SerializeEDKCiphertext(AESEncryptOutput)

      ensures
        && output.Success?
        && input.materials.plaintextDataKey.None?
      ==>
        && var plaintextDataKey := Seq.Last(Seq.DropLast(cryptoPrimitives.History.GenerateRandomBytes)).output.value;
        && var AESEncryptInput := Seq.Last(cryptoPrimitives.History.AESEncrypt).input;
        && AESEncryptInput.msg == plaintextDataKey
        && output.value.materials.plaintextDataKey.value == plaintextDataKey

      ensures
        && output.Success?
        && input.materials.plaintextDataKey.Some?
      ==>
        && Seq.Last(cryptoPrimitives.History.AESEncrypt).input.msg
          == input.materials.plaintextDataKey.value

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //= type=implication
      //# If the keyring cannot serialize
      //# the encryption context, OnEncrypt MUST fail.
      ensures EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> output.Failure?
    {
      var materials := input.materials;
      var suite := materials.algorithmSuite;
      var aad :- EncryptionContextToAAD(materials.encryptionContext);

      // Random is a method, and transitions require both a key and encrypted data key
      var randomKeyResult := cryptoPrimitives
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(suite)));
      var k' :- randomKeyResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      var randomIvResult := cryptoPrimitives
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := wrappingAlgorithm.ivLength));
      var iv :- randomIvResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
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

      :- Need(|wrappingKey|== wrappingAlgorithm.keyLength as int,
        Types.AwsCryptographicMaterialProvidersException( message := "Wrapping key length does not match algorithm"));

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST encrypt the plaintext data key in the encryption
      //# materials (structures.md#encryption-materials) using AES-GCM.
      var aesEncryptResult := cryptoPrimitives
        .AESEncrypt(
          Crypto.AESEncryptInput(
            encAlg := wrappingAlgorithm,
            iv := iv ,
            key := wrappingKey ,
            msg := plaintextDataKey ,
            aad := aad 
          )
      );
      var encryptResult :- aesEncryptResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      var encryptedKey := SerializeEDKCiphertext(encryptResult);

      :- Need(HasUint16Len(providerInfo),
        Types.AwsCryptographicMaterialProvidersException( message := "Serialized provider info too long."));
      :- Need(HasUint16Len(encryptedKey),
        Types.AwsCryptographicMaterialProvidersException( message := "Encrypted data key too long."));

      var edk: Types.EncryptedDataKey := Types.EncryptedDataKey(
        keyProviderId := keyNamespace,
        keyProviderInfo := providerInfo,
        ciphertext := encryptedKey);

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# The keyring MUST append the constructed encrypted data key to the
      //# encrypted data key list in the encryption materials
      //# (structures.md#encryption-materials).

      //= compliance/framework/raw-aes-keyring.txt#2.7.1
      //# OnEncrypt MUST output the modified encryption materials
      //# (structures.md#encryption-materials).
      var nextMaterials :- if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk])
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
      var result := Types.OnEncryptOutput(materials := nextMaterials);
      return Success(result);
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>){true}

    //= compliance/framework/raw-aes-keyring.txt#2.7.2
    //= type=implication
    //# OnDecrypt MUST take decryption materials (structures.md#decryption-
    //# materials) and a list of encrypted data keys
    //# (structures.md#encrypted-data-key) as input.
    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (output: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures output.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          output.value.materials
        )
      // TODO: ensure non-None when input edk list has edk with valid provider info

      // Plaintext decrypted using expected AAD
      ensures
        && output.Success?
      ==>
        && input.materials.plaintextDataKey.None?
        && output.value.materials.plaintextDataKey.Some?
        && 0 < |cryptoPrimitives.History.AESDecrypt|
        && Seq.Last(cryptoPrimitives.History.AESDecrypt).output.Success?
        && EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && var AESDecryptRequest := Seq.Last(cryptoPrimitives.History.AESDecrypt).input;
        && AESDecryptRequest.encAlg == wrappingAlgorithm
        && AESDecryptRequest.key == wrappingKey
        && (exists edk
          | edk in input.encryptedDataKeys
          :: 
            && ValidProviderInfo(edk.keyProviderInfo)
            && wrappingAlgorithm.tagLength as nat <= |edk.ciphertext|
            && var encryptionOutput := DeserializeEDKCiphertext(
              edk.ciphertext,
              wrappingAlgorithm.tagLength as nat
            );
            && AESDecryptRequest.cipherTxt == encryptionOutput.cipherText
            && AESDecryptRequest.authTag == encryptionOutput.authTag
            && AESDecryptRequest.iv == GetIvFromProvInfo(edk.keyProviderInfo)
        )
        && AESDecryptRequest.aad == EncryptionContextToAAD(input.materials.encryptionContext).value
        && output.value.materials.plaintextDataKey.value
          == Seq.Last(cryptoPrimitives.History.AESDecrypt).output.value;

      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //= type=implication
      //# If the keyring cannot
      //# serialize the encryption context, OnDecrypt MUST fail.
      ensures EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> output.Failure?
    {
      var materials := input.materials;
      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException( message := "Keyring received decryption materials that already contain a plaintext data key."));

      var aad :- EncryptionContextToAAD(input.materials.encryptionContext);
      :- Need(|wrappingKey|== wrappingAlgorithm.keyLength as int,
        Types.AwsCryptographicMaterialProvidersException( message := "The wrapping key does not match the wrapping algorithm"));

      var errors: seq<Types.Error> := [];
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# The keyring MUST perform the following actions on each encrypted data
      //# key (structures.md#encrypted-data-key) in the input encrypted data
      //# key list, serially, until it successfully decrypts one.
      for i := 0 to |input.encryptedDataKeys|
        invariant |errors| == i
        invariant unchanged(History)
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
            :- Need(
              GetEncryptKeyLength(materials.algorithmSuite) as nat == |ptKeyRes.Extract()|,
              // this should never happen
              Types.AwsCryptographicMaterialProvidersException( message := "Plaintext Data Key is not the expected length"));
            //= compliance/framework/raw-aes-keyring.txt#2.7.2
            //# If a decryption succeeds, this keyring MUST add the resulting
            //# plaintext data key to the decryption materials and return the
            //# modified materials.
            var result :- Materials.DecryptionMaterialsAddDataKey(materials, ptKeyRes.Extract());
            var value := Types.OnDecryptOutput(materials := result);
            return Success(value);
          } else {
            errors := errors + [ptKeyRes.error];
          }
        } else {
          errors := errors + [
            Types.AwsCryptographicMaterialProvidersException( 
              message :="EncrypedDataKey "
              + Base10Int2String(i)
              + " did not match AESKeyring. " )
          ];
        }
      }
      //= compliance/framework/raw-aes-keyring.txt#2.7.2
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      return Failure(Types.Collection(list := errors));
    }

    //TODO This needs to be a private method
    method Decrypt(
      iv: seq<uint8>,
      encryptionOutput: Crypto.AESEncryptOutput,
      encryptionContext: Types.EncryptionContext
    ) returns (res: Result<seq<uint8>, Types.Error>)
      requires |encryptionOutput.authTag| == wrappingAlgorithm.tagLength as int
      requires |wrappingKey| == wrappingAlgorithm.keyLength as int
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures unchanged(History)
      ensures
        res.Success?
      ==>
        && |old(cryptoPrimitives.History.AESDecrypt)| + 1 == |cryptoPrimitives.History.AESDecrypt|
        && Seq.Last(cryptoPrimitives.History.AESDecrypt).output.Success?
        && EncryptionContextToAAD(encryptionContext).Success?
        && var AESDecryptRequest := Seq.Last(cryptoPrimitives.History.AESDecrypt).input;
        && AESDecryptRequest.encAlg == wrappingAlgorithm
        && AESDecryptRequest.key == wrappingKey
        && AESDecryptRequest.cipherTxt == encryptionOutput.cipherText
        && AESDecryptRequest.authTag == encryptionOutput.authTag
        && AESDecryptRequest.iv == iv
        && AESDecryptRequest.aad == EncryptionContextToAAD(encryptionContext).value
        && res.value
          == Seq.Last(cryptoPrimitives.History.AESDecrypt).output.value;
    {
      :- Need(|iv| == wrappingAlgorithm.ivLength as int, Types.AwsCryptographicMaterialProvidersException( message := ""));
      var aad :- EncryptionContextToAAD(encryptionContext);
      var maybePtKey := cryptoPrimitives
        .AESDecrypt(
          Crypto.AESDecryptInput(
            encAlg := wrappingAlgorithm,
            key := wrappingKey,
            cipherTxt := encryptionOutput.cipherText,
            authTag := encryptionOutput.authTag,
            iv := iv,
            aad := aad
          )
      );
      var ptKey :- maybePtKey.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      return Success(ptKey);
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires |iv| == wrappingAlgorithm.ivLength as int
    {
        keyName +
        UInt32ToSeq((wrappingAlgorithm.tagLength * 8) as uint32) + // tag length in bits
        UInt32ToSeq(wrappingAlgorithm.ivLength as uint32) + // IV length in bytes
        iv
    }

    // TODO bring in the broken up spec statements
    predicate method ShouldDecryptEDK(edk: Types.EncryptedDataKey) {
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
  ): ( encOutput: Crypto.AESEncryptOutput)
    requires tagLen <= |ciphertext|
    ensures |encOutput.authTag| == tagLen
    ensures SerializeEDKCiphertext(encOutput) == ciphertext
  {
      var encryptedKeyLength := |ciphertext| - tagLen as int;
      Crypto.AESEncryptOutput(
        cipherText := ciphertext[.. encryptedKeyLength],
        authTag := ciphertext[encryptedKeyLength ..])
  }

  function method SerializeEDKCiphertext(encOutput: Crypto.AESEncryptOutput): (ciphertext: seq<uint8>) {
    encOutput.cipherText + encOutput.authTag
  }

  lemma EDKSerializeDeserialize(encOutput: Crypto.AESEncryptOutput)
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
    encryptionContext: Types.EncryptionContext
  ):
    (res: Result<seq<uint8>, Types.Error>)
  {
    :- Need(|encryptionContext| < UINT16_LIMIT,
      Types.AwsCryptographicMaterialProvidersException( message := "Encryption Context is too large" ));
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
        :- Need(HasUint16Len(k) && HasUint16Len(v),
          Types.AwsCryptographicMaterialProvidersException( message := "Unable to serialize encryption context"));
        Success(UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);

      var pairsBytes :- Seq.MapWithResult(KeyIntoPairBytes, keys);

      // The final return should be the bytes of the pairs, prepended with the number of pairs
      var allBytes := UInt16ToSeq(|keys| as uint16) + Seq.Flatten(pairsBytes);
      Success(allBytes)
  }
}
