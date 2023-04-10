// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../Materials.dfy"
include "../KeyWrapping/MaterialWrapping.dfy"
include "../KeyWrapping/EdkWrapping.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module RawRSAKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened String = StandardLibrary.String
  import opened Actions
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import Crypto = AwsCryptographyPrimitivesTypes
  import Aws.Cryptography.Primitives
  import Keyring
  import Materials
  import opened AlgorithmSuites
  import Random
  import RSAEncryption
  import UTF8
  import opened Seq
  import MaterialWrapping
  import EdkWrapping


  //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#public-key
  //= type=TODO
  //# The raw RSA keyring SHOULD support loading PEM
  //# encoded [X.509 SubjectPublicKeyInfo structures]
  //# (https://tools.ietf.org/html/rfc5280#section-4.1) as public keys.

  class RawRSAKeyring
    extends Keyring.VerifiableInterface, Types.IKeyring
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
    const publicKey: Option<seq<uint8>>
    const privateKey: Option<seq<uint8>>
    const paddingScheme: Crypto.RSAPaddingMode

    //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#initialization
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    //# - [Key Namespace](./keyring-interface.md#key-namespace)
    //# - [Key Name](./keyring-interface.md#key-name)
    //# - [Padding Scheme](#padding-scheme)
    //# - [Public Key](#public-key) and/or [Private Key](#private-key)
    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#public-key
      //= type=TODO
      //# The public key MUST follow the [RSA specification for public keys](#rsa)
      // NOTE: section 2.4.2 is a lie,
      // See https://datatracker.ietf.org/doc/html/rfc8017#section-3.1 instead
      // NOTE: A sequence of uint8 is NOT how a public key is stored according to the RFC linked, though it is how the libraries we use define them
      publicKey: Option<seq<uint8>>,

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#private-key
      //= type=TODO
      //# The private key MUST follow the [RSA specification for private keys](#rsa)
      // NOTE: section 2.4.2 is a lie,
      // See https://datatracker.ietf.org/doc/html/rfc8017#section-3.2 instead
      // NOTE: A sequence of uint8s is NOT how a public key is stored according to the RFC linked, though it is how the libraries we use define them
      privateKey: Option<seq<uint8>>,

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#private-key
      //= type=TODO
      //# The
      //# private key SHOULD contain all Chinese Remainder Theorem (CRT)
      //# components (public exponent, prime factors, CRT exponents, and CRT
      //# coefficient).
      // NOTE: What? Shouldn't the above be on the Cryptographic library?
      // i.e.: BouncyCastle, pyca, etc.?

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#padding-scheme
      //= type=implication
      //# This value MUST correspond with one of the [supported padding schemes]
      //# (#supported-padding-schemes).
      paddingScheme: Crypto.RSAPaddingMode,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires |namespace| < UINT16_LIMIT
      requires |name| < UINT16_LIMIT
      requires cryptoPrimitives.ValidState()
      ensures this.keyNamespace == namespace
      ensures this.keyName == name
      ensures this.paddingScheme == paddingScheme
      ensures this.publicKey == publicKey
      ensures this.privateKey == privateKey
      ensures ValidState() && fresh(History) && fresh(Modifies - cryptoPrimitives.Modifies)
    {
      this.keyNamespace := namespace;
      this.keyName := name;
      this.paddingScheme := paddingScheme;
      this.publicKey := publicKey;
      this.privateKey := privateKey;

      this.cryptoPrimitives := cryptoPrimitives;

      History := new Types.IKeyringCallHistory();
      Modifies := { History } + cryptoPrimitives.Modifies;
    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>) {true}

    //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials](structures.md#encryption-
    //# materials) as input.
    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (output: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures
        output.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          output.value.materials
        )

     //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
     //= type=implication
     //# OnEncrypt MUST fail if this keyring does not have a specified [public
     //# key](#public-key).
     ensures
       this.publicKey.None? || |this.publicKey.Extract()| == 0
     ==>
       output.Failure?

     //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
     //= type=implication
     //# If the [encryption materials](structures.md#encryption-materials) do
     //# not contain a plaintext data key, OnEncrypt MUST generate a random
     //# plaintext data key and set it on the [encryption materials]
     //# (structures.md#encryption-materials).
     ensures
       && input.materials.plaintextDataKey.None?
       && output.Success?
     ==>
       output.value.materials.plaintextDataKey.Some?

     //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
     //= type=implication
     //# If RSA encryption was successful, OnEncrypt MUST return the input
     //# [encryption materials](structures.md#encryption-materials), modified
     //# in the following ways:
     //# - The encrypted data key list has a new encrypted data key added,
     //#   constructed as follows:
     ensures
       && output.Success?
     ==>
       |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1

     //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
     //= type=implication
     //# The keyring MUST NOT derive a public key from a
     //# specified [private key](#private-key).
     // NOTE: Attempting to proove this by stating that a Keyring
     // without a public key but with a private key will not encrypt
     ensures
       this.privateKey.Some? && this.publicKey.None?
     ==>
       output.Failure?
    {
      :- Need(
        this.publicKey.Some? && |this.publicKey.Extract()| > 0,
        Types.AwsCryptographicMaterialProvidersException(
          message := "A RawRSAKeyring without a public key cannot provide OnEncrypt"));

      var materials := input.materials;
      var suite := materials.algorithmSuite;

      var wrap := new RsaWrapKeyMaterial(
        publicKey.value,
        paddingScheme,
        cryptoPrimitives
      );
      var generateAndWrap := new RsaGenerateAndWrapKeyMaterial(
        publicKey.value,
        paddingScheme,
        cryptoPrimitives
      );

      var wrapOutput :- EdkWrapping.WrapEdkMaterial<RsaWrapInfo>(
        encryptionMaterials := materials,
        wrap := wrap,
        generateAndWrap := generateAndWrap
      );
      var symmetricSigningKeyList :=
        if wrapOutput.symmetricSigningKey.Some? then
          Some([wrapOutput.symmetricSigningKey.value])
        else
          None;

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
      //# If RSA encryption was successful, OnEncrypt MUST return the input
      //# [encryption materials](structures.md#encryption-materials), modified
      //# in the following ways:
      //# - The encrypted data key list has a new encrypted data key added,
      //#   constructed as follows:
      var edk: Types.EncryptedDataKey := Types.EncryptedDataKey(

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //#  -  The [key provider ID](structures.md#key-provider-id) field is
        //#     this keyring's [key namespace](keyring-interface.md#key-
        //#     namespace).
        keyProviderId := this.keyNamespace,

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //#  -  The [key provider information](structures.md#key-provider-
        //#     information) field is this keyring's [key name](keyring-
        //#     interface.md#key-name).
        keyProviderInfo := this.keyName,

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //#  -  The [ciphertext](structures.md#ciphertext) field is the
        //#     ciphertext output by the RSA encryption of the plaintext data
        //#     key.
        ciphertext := wrapOutput.wrappedMaterial
      );

      if (wrapOutput.GenerateAndWrapEdkMaterialOutput?) {
        var result :- Materials.EncryptionMaterialAddDataKey(materials, wrapOutput.plaintextDataKey, [edk], symmetricSigningKeyList);
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

    //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
    //= type=implication
    //# OnDecrypt MUST take [decryption materials](structures.md#decryption-
    //# materials) and a list of [encrypted data keys]
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

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
      //= type=implication
      //# OnDecrypt MUST fail if this keyring does not have a specified [private
      //# key](#private-key).
      ensures
        privateKey.None? || |privateKey.Extract()| == 0
      ==>
        output.Failure?

      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
      //= type=implication
      //# If the decryption materials already contain a plaintext data key, the
      //# keyring MUST fail and MUST NOT modify the [decryption materials]
      //# (structures.md#decryption-materials).
      ensures
        input.materials.plaintextDataKey.Some?
      ==>
        output.Failure?
    {
      :- Need(
        this.privateKey.Some? && |this.privateKey.Extract()| > 0,
        Types.AwsCryptographicMaterialProvidersException(
          message := "A RawRSAKeyring without a private key cannot provide OnEncrypt"));

      var materials := input.materials;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring received decryption materials that already contain a plaintext data key."));

      var errors: seq<Types.Error> := [];
      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
      //# The keyring MUST attempt to decrypt the input encrypted data keys, in
      //# list order, until it successfully decrypts one.
      for i := 0 to |input.encryptedDataKeys|
        invariant |errors| == i
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          var edk := input.encryptedDataKeys[i];

          var unwrap := new RsaUnwrapKeyMaterial(
            privateKey.Extract(),
            paddingScheme,
            cryptoPrimitives
          );
          var unwrapOutput := EdkWrapping.UnwrapEdkMaterial(
            edk.ciphertext,
            materials,
            unwrap
          );

          //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
          //# If any decryption succeeds, this keyring MUST immediately return the
          //# input [decryption materials](structures.md#decryption-materials),
          //# modified in the following ways:
          if unwrapOutput.Success? {
            //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
            //# - The output of RSA decryption is set as the decryption material's
            //#   plaintext data key.
            var returnMaterials :- Materials.DecryptionMaterialsAddDataKey(
              materials,
              unwrapOutput.value.plaintextDataKey,
              unwrapOutput.value.symmetricSigningKey
            );
            return Success(Types.OnDecryptOutput(materials := returnMaterials));
          } else {
            errors := errors + [unwrapOutput.error];
          }
        } else {
          errors := errors + [Types.AwsCryptographicMaterialProvidersException( message :=
            "EncryptedDataKey "
            + Base10Int2String(i)
            + " did not match RSAKeyring. ")
          ];
        }
      }
      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the [decryption materials](structures.md#decryption-materials).
      return Failure(Types.CollectionOfErrors(list := errors));
    }

    predicate method ShouldDecryptEDK(edk: Types.EncryptedDataKey)
      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
      //= type=implication
      //# For each encrypted data key, the keyring MUST attempt to decrypt the
      //# encrypted data key into plaintext using RSA if and only if the
      //# following is true:
      ensures
        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
        //= type=implication
        //# - The encrypted data key's [key provider information]
        //#   (structures.md#key-provider-information). has a value equal to
        //#   this keyring's [key name](keyring-interface.md#key-name).
        && edk.keyProviderInfo == this.keyName

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#ondecrypt
        //= type=implication
        //# - The encrypted data key's [key provider ID](structures.md#key-
        //#   provider-id) has a value equal to this keyring's [key namespace]
        //#   (keyring-interface.md#key-namespace).
        && edk.keyProviderId == this.keyNamespace

        && |edk.ciphertext| > 0
      ==>
        true
    {
      && UTF8.ValidUTF8Seq(edk.keyProviderInfo)
      && edk.keyProviderInfo == this.keyName
      && edk.keyProviderId == this.keyNamespace
      && |edk.ciphertext| > 0
    }
  }

  datatype RsaUnwrapInfo = RsaUnwrapInfo()

  datatype RsaWrapInfo = RsaWrapInfo()

  class RsaGenerateAndWrapKeyMaterial
    extends MaterialWrapping.GenerateAndWrapMaterial<RsaWrapInfo>
  {
    const publicKey: seq<uint8>
    const paddingScheme: Crypto.RSAPaddingMode
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    constructor(
      publicKey: seq<uint8>,
      paddingScheme: Crypto.RSAPaddingMode,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires cryptoPrimitives.ValidState()
      ensures
        && this.publicKey == publicKey
        && this.paddingScheme == paddingScheme
        && this.cryptoPrimitives == cryptoPrimitives
      ensures Invariant()
    {
      this.publicKey := publicKey;
      this.paddingScheme := paddingScheme;
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
      input: MaterialWrapping.GenerateAndWrapInput,
      res: Result<MaterialWrapping.GenerateAndWrapOutput<RsaWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<RsaWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
    }

    method Invoke(
      input: MaterialWrapping.GenerateAndWrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<RsaWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<RsaWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.plaintextMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
      //# If the [encryption materials](structures.md#encryption-materials) do
      //# not contain a plaintext data key, OnEncrypt MUST generate a random
      //# plaintext data key and set it on the [encryption materials]
      //# (structures.md#encryption-materials).
      var generateBytesResult := cryptoPrimitives.GenerateRandomBytes(
        Crypto.GenerateRandomBytesInput(
          length := AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite)
        )
      );
      var plaintextMaterial :- generateBytesResult.MapFailure(
        e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e)
      );
      
      var wrap := new RsaWrapKeyMaterial(
        publicKey,
        paddingScheme,
        cryptoPrimitives
      );

      var wrapOutput: MaterialWrapping.WrapOutput<RsaWrapInfo> :- wrap.Invoke(
        MaterialWrapping.WrapInput(
          plaintextMaterial := plaintextMaterial,
          algorithmSuite := input.algorithmSuite,
          encryptionContext := input.encryptionContext
        ), []);

      var output := MaterialWrapping.GenerateAndWrapOutput(
        plaintextMaterial := plaintextMaterial,
        wrappedMaterial := wrapOutput.wrappedMaterial,
        wrapInfo := RsaWrapInfo()
      );

      return Success(output);
    }
  }

  class RsaWrapKeyMaterial
    extends MaterialWrapping.WrapMaterial<RsaWrapInfo>
  {
    const publicKey: seq<uint8>
    const paddingScheme: Crypto.RSAPaddingMode
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    constructor(
      publicKey: seq<uint8>,
      paddingScheme: Crypto.RSAPaddingMode,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires cryptoPrimitives.ValidState()
      ensures
        && this.publicKey == publicKey
        && this.paddingScheme == paddingScheme
        && this.cryptoPrimitives == cryptoPrimitives
      ensures Invariant()
    {
      this.publicKey := publicKey;
      this.paddingScheme := paddingScheme;
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
      res: Result<MaterialWrapping.WrapOutput<RsaWrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<RsaWrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && (res.Success?
      ==>
        && Invariant()
        && 0 < |cryptoPrimitives.History.RSAEncrypt|
        && Seq.Last(cryptoPrimitives.History.RSAEncrypt).output.Success?
        && var RsaEncryptInput := Seq.Last(cryptoPrimitives.History.RSAEncrypt).input;
        && var RsaEncryptOutput := Seq.Last(cryptoPrimitives.History.RSAEncrypt).output;
        && RsaEncryptInput.padding == paddingScheme
        && RsaEncryptInput.publicKey == publicKey
        && RsaEncryptInput.plaintext == input.plaintextMaterial
        && RsaEncryptOutput.value == res.value.wrappedMaterial
      )
    }

    method Invoke(
      input: MaterialWrapping.WrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.WrapInput, Result<MaterialWrapping.WrapOutput<RsaWrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.WrapOutput<RsaWrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
    {
      //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
      //# The keyring MUST attempt to encrypt the plaintext data key in the
      //# [encryption materials](structures.md#encryption-materials) using RSA.
      //# The keyring performs [RSA encryption](#rsa) with the
      //# following specifics:
      var RSAEncryptOutput := cryptoPrimitives.RSAEncrypt(Crypto.RSAEncryptInput(
        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //# - This keyring's [padding scheme](#supported-padding-schemes) is the RSA padding
        //#   scheme.
        padding := paddingScheme,

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //# - This keyring's [public key](#public-key) is the RSA public key.
        publicKey := publicKey,

        //= aws-encryption-sdk-specification/framework/raw-rsa-keyring.md#onencrypt
        //# - The plaintext data key is the plaintext input to RSA encryption.
        plaintext := input.plaintextMaterial
      ));

      var ciphertext :- RSAEncryptOutput.MapFailure(e => Types.AwsCryptographyPrimitives(e));

      var output := MaterialWrapping.WrapOutput(
        wrappedMaterial := ciphertext,
        wrapInfo := RsaWrapInfo()
      );

      return Success(output);
    }
  }

  class RsaUnwrapKeyMaterial
    extends MaterialWrapping.UnwrapMaterial<RsaUnwrapInfo>
  {
    const privateKey: seq<uint8>
    const paddingScheme: Crypto.RSAPaddingMode
    const cryptoPrimitives: Primitives.AtomicPrimitivesClient

    constructor(
      privateKey: seq<uint8>,
      paddingScheme: Crypto.RSAPaddingMode,
      cryptoPrimitives: Primitives.AtomicPrimitivesClient
    )
      requires cryptoPrimitives.ValidState()
      ensures
        && this.privateKey == privateKey
        && this.paddingScheme == paddingScheme
        && this.cryptoPrimitives == cryptoPrimitives
      ensures Invariant()
    {
      this.privateKey := privateKey;
      this.paddingScheme := paddingScheme;
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
      input: MaterialWrapping.UnwrapInput,
      res: Result<MaterialWrapping.UnwrapOutput<RsaUnwrapInfo>, Types.Error>,
      attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<RsaUnwrapInfo>, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && |cryptoPrimitives.History.RSADecrypt| > 0
        && Last(cryptoPrimitives.History.RSADecrypt).output.Success?
        && var decryptInput := Last(cryptoPrimitives.History.RSADecrypt).input;
        && var decryptOutput := Last(cryptoPrimitives.History.RSADecrypt).output.value;
        && decryptInput.padding == paddingScheme
        && decryptInput.privateKey == privateKey
        && decryptInput.cipherText == input.wrappedMaterial
        && decryptOutput == res.value.unwrappedMaterial
    }
    
    method Invoke(
      input: MaterialWrapping.UnwrapInput,
      ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<RsaUnwrapInfo>, Types.Error>>>
    ) returns (res: Result<MaterialWrapping.UnwrapOutput<RsaUnwrapInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==>
        |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
    {
      var suite := input.algorithmSuite;
      var wrappedMaterial := input.wrappedMaterial;
      var aad := input.encryptionContext;

      var maybeDecryptResult := cryptoPrimitives.RSADecrypt(Crypto.RSADecryptInput(
        padding := paddingScheme,
        privateKey := privateKey,
        cipherText := wrappedMaterial
      ));

      var decryptResult :-  maybeDecryptResult
        .MapFailure(e => Types.AwsCryptographyPrimitives( AwsCryptographyPrimitives := e ));
      
      :- Need(
        |decryptResult| == AlgorithmSuites.GetEncryptKeyLength(suite) as nat,
         Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid plaintext length.")
      );
      
      assert |cryptoPrimitives.History.RSADecrypt| > 0;

      var output := MaterialWrapping.UnwrapOutput(
        unwrappedMaterial := decryptResult,
        unwrapInfo := RsaUnwrapInfo()
      );
      
      return Success(output);
    }
  }
}
