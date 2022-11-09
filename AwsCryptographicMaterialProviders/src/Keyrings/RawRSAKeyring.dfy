// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Keyring.dfy"
include "../Materials.dfy"
include "../AlgorithmSuites.dfy"
include "../../../src/StandardLibrary/String.dfy"
include "../AlgorithmSuites.dfy"
include "../Materials.dfy"
include "../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

module RawRSAKeyring {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened String = StandardLibrary.String
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
  import Seq

  //= compliance/framework/raw-rsa-keyring.txt#2.5.2
  //= type=TODO
  //# The raw RSA keyring SHOULD support loading PEM
  //# encoded X.509 SubjectPublicKeyInfo structures
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

    //= compliance/framework/raw-rsa-keyring.txt#2.5
    //= type=implication
    //# On keyring initialization, the caller MUST provide the following:
    //#*  Key Namespace (./keyring-interface.md#key-namespace)
    //#*  Key Name (./keyring-interface.md#key-name)
    //#*  Padding Scheme (Section 2.5.1)
    //#*  Public Key (Section 2.5.2) and/or Private Key (Section 2.5.3)
    constructor (
      namespace: UTF8.ValidUTF8Bytes,
      name: UTF8.ValidUTF8Bytes,

      //= compliance/framework/raw-rsa-keyring.txt#2.5.2
      //= type=TODO
      //# The public key MUST follow the RSA specification for public keys
      //# (Section 2.4.2).
      // NOTE: section 2.4.2 is a lie,
      // See https://datatracker.ietf.org/doc/html/rfc8017#section-3.1 instead
      // NOTE: A sequence of uint8 is NOT how a public key is stored according to the RFC linked, though it is how the libraries we use define them
      publicKey: Option<seq<uint8>>,

      //= compliance/framework/raw-rsa-keyring.txt#2.5.3
      //= type=TODO
      //# The private key MUST follow the RSA specification for private keys
      //# (Section 2.4.2).
      // NOTE: section 2.4.2 is a lie,
      // See https://datatracker.ietf.org/doc/html/rfc8017#section-3.2 instead
      // NOTE: A sequence of uint8s is NOT how a public key is stored according to the RFC linked, though it is how the libraries we use define them
      privateKey: Option<seq<uint8>>,

      //= compliance/framework/raw-rsa-keyring.txt#2.5.3
      //= type=TODO
      //# The
      //# private key SHOULD contain all Chinese Remainder Theorem (CRT)
      //# components (public exponent, prime factors, CRT exponents, and CRT
      //# coefficient).
      // NOTE: What? Shouldn't the above be on the Cryptographic library?
      // i.e.: BouncyCastle, pyca, etc.?

      //= compliance/framework/raw-rsa-keyring.txt#2.5.1
      //= type=implication
      //# This value MUST correspond with one of the supported padding schemes
      //# (Section 2.5.1.1).
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

    //= compliance/framework/raw-rsa-keyring.txt#2.6.1
    //= type=implication
    //# OnEncrypt MUST take encryption materials (structures.md#encryption-
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

     //= compliance/framework/raw-rsa-keyring.txt#2.6.1
     //= type=implication
     //# OnEncrypt MUST fail if this keyring does not have a specified public
     //# key (Section 2.5.2).
     ensures
       this.publicKey.None? || |this.publicKey.Extract()| == 0
     ==>
       output.Failure?

     //= compliance/framework/raw-rsa-keyring.txt#2.6.1
     //= type=implication
     //# If the encryption materials (structures.md#encryption-materials) do
     //# not contain a plaintext data key, OnEncrypt MUST generate a random
     //# plaintext data key and set it on the encryption materials
     //# (structures.md#encryption-materials).
     ensures
       && input.materials.plaintextDataKey.None?
       && output.Success?
     ==>
       output.value.materials.plaintextDataKey.Some?

     //= compliance/framework/raw-rsa-keyring.txt#2.6.1
     //= type=implication
     //# If RSA encryption was successful, OnEncrypt MUST return the input
     //# encryption materials (structures.md#encryption-materials), modified
     //# in the following ways:
     //#*  The encrypted data key list has a new encrypted data key added,
     //#   constructed as follows:
     ensures
       && output.Success?
     ==>
       |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1

     //= compliance/framework/raw-rsa-keyring.txt#2.6.1
     //= type=implication
     //# The keyring MUST NOT derive a public key from a
     //# specified private key (Section 2.5.3).
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

      // While this may be an unnecessary operation, it is more legiable to generate
      // and then maybe use this new plain text datakey then generate it in the if statement
      var generateBytesResult := cryptoPrimitives
        .GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := GetEncryptKeyLength(suite)));
      var newPlaintextDataKey :- generateBytesResult.MapFailure(e => Types.AwsCryptographyPrimitives(AwsCryptographyPrimitives := e));

      //= compliance/framework/raw-rsa-keyring.txt#2.6.1
      //# If the encryption materials (structures.md#encryption-materials) do
      //# not contain a plaintext data key, OnEncrypt MUST generate a random
      //# plaintext data key and set it on the encryption materials
      //# (structures.md#encryption-materials).
      var plaintextDataKey :=
        if materials.plaintextDataKey.Some? && |materials.plaintextDataKey.Extract()| > 0
        then materials.plaintextDataKey.value
        else newPlaintextDataKey;

      //= compliance/framework/raw-rsa-keyring.txt#2.6.1
      //# The keyring MUST attempt to encrypt the plaintext data key in the
      //# encryption materials (structures.md#encryption-materials) using RSA.
      //# The keyring performs RSA encryption (Section 2.4.2) with the
      //# following specifics:
      var RSAEncryptOutput := cryptoPrimitives.RSAEncrypt(Crypto.RSAEncryptInput(
        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#*  This keyring's padding scheme (Section 2.5.1.1) is the RSA padding
        //#   scheme.
        padding := paddingScheme,

        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#*  This keyring's public key (Section 2.5.2) is the RSA public key.
        publicKey := publicKey.Extract(),

        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#*  The plaintext data key is the plaintext input to RSA encryption.
        plaintext := plaintextDataKey
      ));

      var ciphertext :- RSAEncryptOutput.MapFailure(e => Types.AwsCryptographyPrimitives(e));

      //= compliance/framework/raw-rsa-keyring.txt#2.6.1
      //# If RSA encryption was successful, OnEncrypt MUST return the input
      //# encryption materials (structures.md#encryption-materials), modified
      //# in the following ways:
      //#*  The encrypted data key list has a new encrypted data key added,
      //#   constructed as follows:
      var edk: Types.EncryptedDataKey := Types.EncryptedDataKey(

        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#  -  The key provider ID (structures.md#key-provider-id) field is
        //#     this keyring's key namespace (keyring-interface.md#key-
        //#     namespace).
        keyProviderId := this.keyNamespace,

        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#  -  The key provider information (structures.md#key-provider-
        //#     information) field is this keyring's key name (keyring-
        //#     interface.md#key-name).
        keyProviderInfo := this.keyName,

        //= compliance/framework/raw-rsa-keyring.txt#2.6.1
        //#  -  The ciphertext (structures.md#ciphertext) field is the
        //#     ciphertext output by the RSA encryption of the plaintext data
        //#     key.
        ciphertext := ciphertext
      );

      var returnMaterials :- if materials.plaintextDataKey.None? then
        Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk])
      else
        Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
      return Success(Types.OnEncryptOutput(materials := returnMaterials));
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>){true}

    //= compliance/framework/raw-rsa-keyring.txt#2.6.2
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

      //= compliance/framework/raw-rsa-keyring.txt#2.6.2
      //= type=implication
      //# OnDecrypt MUST fail if this keyring does not have a specified private
      //# key (Section 2.5.3).
      ensures
        privateKey.None? || |privateKey.Extract()| == 0
      ==>
        output.Failure?

      //= compliance/framework/raw-rsa-keyring.txt#2.6.2
      //= type=implication
      //# If the decryption materials already contain a plaintext data key, the
      //# keyring MUST fail and MUST NOT modify the decryption materials
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
      //= compliance/framework/raw-rsa-keyring.txt#2.6.2
      //# The keyring MUST attempt to decrypt the input encrypted data keys, in
      //# list order, until it successfully decrypts one.
      for i := 0 to |input.encryptedDataKeys|
        invariant |errors| == i
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          var edk := input.encryptedDataKeys[i];
          var decryptResult := cryptoPrimitives.RSADecrypt(Crypto.RSADecryptInput(
            padding := paddingScheme,
            privateKey := privateKey.Extract(),
            cipherText := edk.ciphertext
          ));

          //= compliance/framework/raw-rsa-keyring.txt#2.6.2
          //# If any decryption succeeds, this keyring MUST immediately return the
          //# input decryption materials (structures.md#decryption-materials),
          //# modified in the following ways:
          if decryptResult.Success? {
            //= compliance/framework/raw-rsa-keyring.txt#2.6.2
            //#*  The output of RSA decryption is set as the decryption material's
            //#   plaintext data key.
            var returnMaterials :- Materials.DecryptionMaterialsAddDataKey(
              materials,
              decryptResult.Extract()
            );
            return Success(Types.OnDecryptOutput(materials := returnMaterials));
          } else {
            errors := errors + [Types.AwsCryptographyPrimitives(decryptResult.error)];
          }
        } else {
          errors := errors + [Types.AwsCryptographicMaterialProvidersException( message :=
            "EncryptedDataKey "
            + Base10Int2String(i)
            + " did not match RSAKeyring. ")
          ];
        }
      }
      //= compliance/framework/raw-rsa-keyring.txt#2.6.2
      //# If no decryption succeeds, the keyring MUST fail and MUST NOT modify
      //# the decryption materials (structures.md#decryption-materials).
      return Failure(Types.Collection(list := errors));
    }

    predicate method ShouldDecryptEDK(edk: Types.EncryptedDataKey)
      //= compliance/framework/raw-rsa-keyring.txt#2.6.2
      //= type=implication
      //# For each encrypted data key, the keyring MUST attempt to decrypt the
      //# encrypted data key into plaintext using RSA if and only if the
      //# following is true:
      ensures
        //= compliance/framework/raw-rsa-keyring.txt#2.6.2
        //= type=implication
        //#*  The encrypted data key's key provider information
        //#   (structures.md#key-provider-information). has a value equal to
        //#   this keyring's key name (keyring-interface.md#key-name).
        && edk.keyProviderInfo == this.keyName

        //= compliance/framework/raw-rsa-keyring.txt#2.6.2
        //= type=implication
        //#*  The encrypted data key's key provider ID (structures.md#key-
        //#   provider-id) has a value equal to this keyring's key namespace
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
}
