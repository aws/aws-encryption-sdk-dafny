// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../Materials.dfy"
include "../KeyWrapping/MaterialWrapping.dfy"
include "../KeyWrapping/EdkWrapping.dfy"
include "../CanonicalEncryptionContext.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module RawAESKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened String = StandardLibrary.String
  import opened Actions
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import Keyring
  import Materials
  import CanonicalEncryptionContext
  import opened AlgorithmSuites
  import UTF8
  import Seq
  import MaterialWrapping
  import EdkWrapping

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
      && |wrappingKey| == wrappingAlgorithm.keyLength as nat
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

    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#wrapping-key
    //# The wrapping key MUST be a secret value consisting of
    //# cryptographically secure pseudo-random bytes.

    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#wrapping-key
    //# It MUST be randomly
    //# generated from a cryptographically secure entropy source.
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: Crypto.AES_GCM

    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#initialization
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

      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#wrapping-key
      //= type=implication
      //# The length
      //# of the wrapping key MUST be 128, 192, or 256.
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

    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials](structures.md#encryption-
    //# materials) as input.
    method {:vcs_split_on_every_assert} OnEncrypt'(input: Types.OnEncryptInput)
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
        // Verify AESEncrypt Input
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && 1 <= |cryptoPrimitives.History.GenerateRandomBytes|
        && Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.Success?
        && var iv :=  Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.value;
        && |iv| == wrappingAlgorithm.ivLength as nat
        && 1 <= |cryptoPrimitives.History.AESEncrypt|
        && var AESEncryptInput := Seq.Last(cryptoPrimitives.History.AESEncrypt).input;
        && AESEncryptInput.encAlg == wrappingAlgorithm
        && AESEncryptInput.key == wrappingKey
        && AESEncryptInput.iv == iv
        && AESEncryptInput.aad == CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).value

        // Verify AESEncrypt output
        && |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && var edk := Seq.Last(output.value.materials.encryptedDataKeys);
        && Seq.Last(cryptoPrimitives.History.AESEncrypt).output.Success?
        && var AESEncryptOutput := Seq.Last(cryptoPrimitives.History.AESEncrypt).output.value;
        && edk.keyProviderInfo == SerializeProviderInfo(iv)
        // Can not prove this at this time because if there is Wrapping involved
        // then this will not be true.
        // && edk.ciphertext == SerializeEDKCiphertext(AESEncryptOutput)

      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
      //= type=implication
      //# If the keyring cannot serialize
      //# the encryption context, OnEncrypt MUST fail.
      ensures CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> output.Failure?
    {
      var materials := input.materials;
      var suite := materials.algorithmSuite;

      var wrap := new AesWrapKeyMaterial(
        wrappingKey,
        wrappingAlgorithm,
        cryptoPrimitives
      );
      var generateAndWrap := new AesGenerateAndWrapKeyMaterial(wrap);

      var wrapOutput :- EdkWrapping.WrapEdkMaterial<AesWrapInfo>(
        encryptionMaterials := materials,
        wrap := wrap,
        generateAndWrap := generateAndWrap
      );

      var symmetricSigningKeyList :=
        if wrapOutput.symmetricSigningKey.Some? then
          Some([wrapOutput.symmetricSigningKey.value])
        else
          None;

      var edk: Types.EncryptedDataKey := Types.EncryptedDataKey(
        keyProviderId := keyNamespace,
        keyProviderInfo := SerializeProviderInfo(wrapOutput.wrapInfo.iv),
        ciphertext := wrapOutput.wrappedMaterial
      );

      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
      //# The keyring MUST append the constructed encrypted data key to the
      //# encrypted data key list in the [encryption materials]
      //# (structures.md#encryption-materials).

      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
      //# OnEncrypt MUST output the modified [encryption materials]
      //# (structures.md#encryption-materials).
      if (wrapOutput.GenerateAndWrapEdkMaterialOutput?) {
        var result :- Materials.EncryptionMaterialAddDataKey(
          materials,
          wrapOutput.plaintextDataKey,
          [edk],
          symmetricSigningKeyList
        );
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      } else if (wrapOutput.WrapOnlyEdkMaterialOutput?) {
        // wrapped existing pdk. Add new edk to materials.
        var result :- Materials.EncryptionMaterialAddEncryptedDataKeys(
          materials,
          [edk],
          symmetricSigningKeyList
        );
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      }
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>){true}

    //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#ondecrypt
    //= type=implication
    //# OnDecrypt MUST take [decryption materials](structures.md#decryption-
    //# materials) and a list of [encrypted data keys]
    //# (structures.md#encrypted-data-key) as input.
    method {:vcs_split_on_every_assert} OnDecrypt'(input: Types.OnDecryptInput)
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

      // Plaintext decrypted using expected AAD
      ensures
        && output.Success?
      ==>
        && input.materials.plaintextDataKey.None?
        && output.value.materials.plaintextDataKey.Some?
        && 0 < |cryptoPrimitives.History.AESDecrypt|
        && Seq.Last(cryptoPrimitives.History.AESDecrypt).output.Success?
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).Success?
        && var AESDecryptRequest := Seq.Last(cryptoPrimitives.History.AESDecrypt).input;
        && AESDecryptRequest.encAlg == wrappingAlgorithm
        && AESDecryptRequest.key == wrappingKey
        && (exists edk
          | edk in input.encryptedDataKeys
          ::
            && ValidProviderInfo(edk.keyProviderInfo)
            && wrappingAlgorithm.tagLength as nat <= |edk.ciphertext|
            && AESDecryptRequest.iv == GetIvFromProvInfo(edk.keyProviderInfo)
        )
        && AESDecryptRequest.aad == CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).value
        // Can not prove this at this timbe because there may be wrapping involved.
        // && output.value.materials.plaintextDataKey.value
        //   == Seq.Last(cryptoPrimitives.History.AESDecrypt).output.value;

      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#ondecrypt
      //= type=implication
      //# If the keyring cannot
      //# serialize the encryption context, OnDecrypt MUST fail.
      ensures CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext).Failure? ==> output.Failure?
    {
      var materials := input.materials;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException( message := "Keyring received decryption materials that already contain a plaintext data key."));

      var aad :- CanonicalEncryptionContext.EncryptionContextToAAD(input.materials.encryptionContext);
      :- Need(|wrappingKey|== wrappingAlgorithm.keyLength as int,
        Types.AwsCryptographicMaterialProvidersException( message := "The wrapping key does not match the wrapping algorithm"));

      var errors: seq<Types.Error> := [];
      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#ondecrypt
      //# The keyring MUST perform the following actions on each encrypted data
      //# key](structures.md#encrypted-data-key) in the input encrypted data
      //# key list, serially, until it successfully decrypts one.
      for i := 0 to |input.encryptedDataKeys|
        invariant |errors| == i
        invariant unchanged(History)
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {

          var edk := input.encryptedDataKeys[i];
          var iv := GetIvFromProvInfo(edk.keyProviderInfo);

          var unwrap := new AesUnwrapKeyMaterial(
            wrappingKey,
            wrappingAlgorithm,
            iv,
            cryptoPrimitives
          );
          var unwrapOutput := EdkWrapping.UnwrapEdkMaterial(
            edk.ciphertext,
            materials,
            unwrap
          );

          if unwrapOutput.Success?
          {
            //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#ondecrypt
            //# If a decryption succeeds, this keyring MUST add the resulting
            //# plaintext data key to the decryption materials and return the
            //# modified materials.
            var result :- Materials.DecryptionMaterialsAddDataKey(
              materials,
              unwrapOutput.value.plaintextDataKey,
              unwrapOutput.value.symmetricSigningKey
            );
            var value := Types.OnDecryptOutput(materials := result);
            return Success(value);
          } else {
            errors := errors + [unwrapOutput.error];
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
      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#ondecrypt
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the [decryption materials](structures.md#decryption-materials).
      return Failure(Types.CollectionOfErrors(list := errors));
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires |iv| == wrappingAlgorithm.ivLength as int
    {
        keyName +
        UInt32ToSeq((wrappingAlgorithm.tagLength * 8) as uint32) + // tag length in bits
        UInt32ToSeq(wrappingAlgorithm.ivLength as uint32) + // IV length in bytes
        iv
    }

    predicate method ShouldDecryptEDK(edk: Types.EncryptedDataKey) {
      // The key provider ID of the encrypted data key has a value equal to this keyring's key namespace.
      && edk.keyProviderId == keyNamespace
      && ValidProviderInfo(edk.keyProviderInfo)
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
    {
      && |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLength as int
      // The key name obtained from the encrypted data key's key provider information has a value equal to this keyring's key name.
      && info[0..|keyName|] == keyName
      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#authentication-tag-length
      //= type=implication
      //# This value MUST match the authentication tag length of the keyring's
      //# configured wrapping algorithm

      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == 128
      && SeqToUInt32(info[|keyName|..|keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLength as uint32 * 8
      && SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLength as uint32
      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#iv-length
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

  datatype AesUnwrapInfo = AesUnwrapInfo()
  datatype AesWrapInfo = AesWrapInfo( iv: seq<uint8> )

  class AesGenerateAndWrapKeyMaterial
    extends MaterialWrapping.GenerateAndWrapMaterial<AesWrapInfo>
  {
    const wrap: AesWrapKeyMaterial

    constructor(
      wrap: AesWrapKeyMaterial
    )
      requires wrap.Invariant()
      ensures this.wrap == wrap
      ensures Invariant()
    {
      this.wrap := wrap;
      Modifies := wrap.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && Modifies == wrap.Modifies
      && wrap.Invariant()
    }

    predicate Ensures(
      input: MaterialWrapping.GenerateAndWrapInput,
      res: Result<MaterialWrapping.GenerateAndWrapOutput<AesWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<AesWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && 2 <= |wrap.cryptoPrimitives.History.GenerateRandomBytes|
        && Seq.Last(Seq.DropLast(wrap.cryptoPrimitives.History.GenerateRandomBytes)).output.Success?
        && var plaintextMaterial := Seq.Last(Seq.DropLast(wrap.cryptoPrimitives.History.GenerateRandomBytes)).output.value;
        && res.value.plaintextMaterial == plaintextMaterial
        && wrap.Ensures(
          MaterialWrapping.WrapInput(
            plaintextMaterial := plaintextMaterial,
            algorithmSuite := input.algorithmSuite,
            encryptionContext := input.encryptionContext
          ),
          Success(MaterialWrapping.WrapOutput(
            wrappedMaterial := res.value.wrappedMaterial,
            wrapInfo := res.value.wrapInfo
          )),
          []
        )
      && |res.value.plaintextMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    }

    method Invoke(
      input: MaterialWrapping.GenerateAndWrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<AesWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<AesWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
    {

      var generateBytesResult := wrap.cryptoPrimitives.GenerateRandomBytes(
        Crypto.GenerateRandomBytesInput(
          length := AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite)
        )
      );
      var plaintextMaterial :- generateBytesResult.MapFailure(
        e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e)
      );

      ghost var oldGenerateRandomBytes := wrap.cryptoPrimitives.History.GenerateRandomBytes;

      var wrapOutput: MaterialWrapping.WrapOutput<AesWrapInfo> :- wrap.Invoke(
        MaterialWrapping.WrapInput(
          plaintextMaterial := plaintextMaterial,
          algorithmSuite := input.algorithmSuite,
          encryptionContext := input.encryptionContext
        ), []);

      res := Success(MaterialWrapping.GenerateAndWrapOutput(
        plaintextMaterial := plaintextMaterial,
        wrappedMaterial := wrapOutput.wrappedMaterial,
        wrapInfo := wrapOutput.wrapInfo
      ));

      // This surgery is unfortunate, but required to forward
      // the history and prove that we used it correctly.
      wrap.cryptoPrimitives.History.GenerateRandomBytes := oldGenerateRandomBytes + [Seq.Last(wrap.cryptoPrimitives.History.GenerateRandomBytes)];

    }

  }

  class AesWrapKeyMaterial
    extends MaterialWrapping.WrapMaterial<AesWrapInfo>
  {
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: Crypto.AES_GCM
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    constructor(
      wrappingKey: seq<uint8>,
      wrappingAlgorithm: Crypto.AES_GCM,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires cryptoPrimitives.ValidState()
      ensures
        && this.wrappingKey == wrappingKey
        && this.wrappingAlgorithm == wrappingAlgorithm
        && this.cryptoPrimitives == cryptoPrimitives
      ensures Invariant()
    {
      this.wrappingKey := wrappingKey;
      this.wrappingAlgorithm := wrappingAlgorithm;
      this.cryptoPrimitives := cryptoPrimitives;
      Modifies := cryptoPrimitives.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && cryptoPrimitives.ValidState()
      && Modifies == cryptoPrimitives.Modifies
    }

    predicate Ensures(
      input: MaterialWrapping.WrapInput,
      res: Result<MaterialWrapping.WrapOutput<AesWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<AesWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && (res.Success?
      ==>
        && Invariant()
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && 0 < |cryptoPrimitives.History.GenerateRandomBytes|
        && 0 < |cryptoPrimitives.History.AESEncrypt|
        && Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.Success?
        && Seq.Last(cryptoPrimitives.History.AESEncrypt).output.Success?
        && var iv :=  Seq.Last(cryptoPrimitives.History.GenerateRandomBytes).output.value;
        && var AESEncryptInput := Seq.Last(cryptoPrimitives.History.AESEncrypt).input;
        && var AESEncryptOutput := Seq.Last(cryptoPrimitives.History.AESEncrypt).output.value;
        && |iv| == wrappingAlgorithm.ivLength as nat
        && AESEncryptInput.encAlg == wrappingAlgorithm
        && AESEncryptInput.key == wrappingKey
        && AESEncryptInput.iv == iv
        && AESEncryptInput.aad == CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).value
        && res.value.wrappedMaterial == SerializeEDKCiphertext(AESEncryptOutput)
        && res.value.wrapInfo.iv == iv
      )
    }

    method Invoke(
      input: MaterialWrapping.WrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<AesWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.WrapOutput<AesWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
    {

      var aad :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
      var randomIvResult := cryptoPrimitives
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := wrappingAlgorithm.ivLength));
      var iv :- randomIvResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      //= aws-encryption-sdk-specification/framework/raw-aes-keyring.md#onencrypt
      //# The keyring MUST encrypt the plaintext data key in the [encryption
      //# materials](structures.md#encryption-materials) using AES-GCM.
      var aesEncryptResult := cryptoPrimitives
        .AESEncrypt(
          Crypto.AESEncryptInput(
            encAlg := wrappingAlgorithm,
            iv := iv ,
            key := wrappingKey ,
            msg := input.plaintextMaterial,
            aad := aad
          )
      );
      var wrappedMaterialResult :- aesEncryptResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));
      var wrappedMaterial := SerializeEDKCiphertext(wrappedMaterialResult);

      return Success(MaterialWrapping.WrapOutput(
        wrappedMaterial := wrappedMaterial,
        wrapInfo := AesWrapInfo(iv)
      ));
    }
  }

  class AesUnwrapKeyMaterial
    extends MaterialWrapping.UnwrapMaterial<AesUnwrapInfo>
  {
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: Crypto.AES_GCM
    const iv: seq<uint8>
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    constructor(
      wrappingKey: seq<uint8>,
      wrappingAlgorithm: Crypto.AES_GCM,
      iv: seq<uint8>,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires cryptoPrimitives.ValidState()
      requires |iv| == wrappingAlgorithm.ivLength as nat
      ensures
        && this.wrappingKey == wrappingKey
        && this.iv == iv
        && this.wrappingAlgorithm == wrappingAlgorithm
        && this.cryptoPrimitives == cryptoPrimitives
      ensures Invariant()
    {
      this.wrappingKey := wrappingKey;
      this.iv := iv;
      this.wrappingAlgorithm := wrappingAlgorithm;
      this.cryptoPrimitives := cryptoPrimitives;
      Modifies := cryptoPrimitives.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && cryptoPrimitives.ValidState()
      && Modifies == cryptoPrimitives.Modifies
      && |iv| == wrappingAlgorithm.ivLength as nat
    }

    predicate Ensures(
      input: MaterialWrapping.UnwrapInput,
      res: Result<MaterialWrapping.UnwrapOutput<AesUnwrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<AesUnwrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
        && CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).Success?
        && wrappingAlgorithm.tagLength as nat <= |input.wrappedMaterial|
        && var encryptionOutput := DeserializeEDKCiphertext(
            input.wrappedMaterial,
            wrappingAlgorithm.tagLength as nat
          );
        && 0 < |cryptoPrimitives.History.AESDecrypt|
        && Seq.Last(cryptoPrimitives.History.AESDecrypt).output.Success?
        && var AESDecryptInput := Seq.Last(cryptoPrimitives.History.AESDecrypt).input;
        && AESDecryptInput.encAlg == wrappingAlgorithm
        && AESDecryptInput.key == wrappingKey
        && AESDecryptInput.cipherTxt == encryptionOutput.cipherText
        && AESDecryptInput.authTag == encryptionOutput.authTag
        && AESDecryptInput.iv == iv
        && AESDecryptInput.aad == CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext).value
        && res.value.unwrappedMaterial
          == Seq.Last(cryptoPrimitives.History.AESDecrypt).output.value
    }

    method Invoke(
      input: MaterialWrapping.UnwrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<AesUnwrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.UnwrapOutput<AesUnwrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
    {
      var aad :- CanonicalEncryptionContext.EncryptionContextToAAD(input.encryptionContext);
      :- Need(
        wrappingAlgorithm.tagLength as nat <= |input.wrappedMaterial|,
        Types.AwsCryptographicMaterialProvidersException( message := "Insufficient data to decrypt."));
      var encryptionOutput := DeserializeEDKCiphertext(
        input.wrappedMaterial,
        wrappingAlgorithm.tagLength as nat
      );
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
      :- Need(
        GetEncryptKeyLength(input.algorithmSuite) as nat == |ptKey|,
        Types.AwsCryptographicMaterialProvidersException( message := "Plaintext Data Key is not the expected length"));

      return Success(MaterialWrapping.UnwrapOutput(
        unwrappedMaterial := ptKey,
        unwrapInfo := AesUnwrapInfo
      ));

    }
  }

}
