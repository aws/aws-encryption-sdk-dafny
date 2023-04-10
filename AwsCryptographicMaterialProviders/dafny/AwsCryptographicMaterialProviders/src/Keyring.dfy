// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Materials.dfy"

module Keyring {
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import Materials

  trait {:termination false} VerifiableInterface
    extends Types.IKeyring
  {
    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (output: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      //= aws-encryption-sdk-specification/framework/keyring-interface.md#onencrypt
      //= type=implication
      //# It MUST modify it with at least one of the following behaviors:
      //# - [Generate data key](#generate-data-key)
      //# - [Encrypt data key](#encrypt-data-key)
      //# If this keyring attempted any of the above behaviors, and successfully completed those behaviors,
      //# it MUST output the modified [encryption materials](structures.md#encryption-materials).
      ensures output.Success?
      ==>
        // See the details of ValidEncryptionMaterialsTransition for the following
        
        //= aws-encryption-sdk-specification/framework/keyring-interface.md#generate-data-key
        //= type=implication
        //# If the [encryption materials](structures.md#encryption-materials) do not contain a plaintext data key,
        //# OnEncrypt MUST generate a data key.
        //# If the encryption materials contain a plaintext data key, OnEncrypt MUST NOT generate a data key.
        //# 
        //# Generate Data Key MUST modify the following fields in the [encryption materials](structures.md#encryption-materials):
        //# 
        //# - [plaintext data key](structures.md#plaintext-data-key)
        //# 
        //# To perform this behavior, the keyring generates a [plaintext data key](structures.md#plaintext-data-key)
        //# and sets the resulting plaintext data key on the [encryption materials](structures.md#encryption-materials).
        //# 
        //# The length of the output plaintext data key MUST be equal to the KDF input length of the [algorithm suite](algorithm-suites.md)
        //# specified in the [encryption materials](structures.md#encryption-materials).
        //# The value of the plaintext data key MUST consist of cryptographically secure (pseudo-)random bits.
        //# 
        //# Note: If the keyring successfully performs this behavior, this means that the keyring MAY then
        //# perform the [Encrypt Data Key](#encrypt-data-key) behavior.

        //= aws-encryption-sdk-specification/framework/keyring-interface.md#encrypt-data-key
        //= type=implication
        //# If the [encryption materials](structures.md#encryption-materials) contain a plaintext data key,
        //# OnEncrypt MUST encrypt a data key.
        //# If the encryption materials do not contain a plaintext data key, OnEncrypt MUST NOT encrypt a data key.
        //# 
        //# Encrypt Data Key MUST modify the following fields in the [encryption materials](structures.md#encryption-materials):
        //# 
        //# - [encrypted data keys](structures.md#encrypted-data-keys)
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          output.value.materials
        )

    method OnDecrypt'(input: Types.OnDecryptInput)
      returns (output: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, output)
      ensures unchanged(History)
      //= aws-encryption-sdk-specification/framework/keyring-interface.md#ondecrypt
      //= type=implication
      //# It MUST modify it with the following behavior:
      //# 
      //# - [Decrypt data key](#decrypt-data-key)
      //# 
      //# If the decryption materials already contain a plaintext data key,
      //# the keyring MUST fail
      //# and MUST NOT modify the [decryption materials](structures.md#decryption-materials).
      //# 
      //# If this keyring attempted the above behavior, and succeeded, it MUST output the modified [decryption materials](structures.md#decryption-materials).
      ensures output.Success?
      ==>
      // See the details of DecryptionMaterialsTransitionIsValid for the following

      //= aws-encryption-sdk-specification/framework/keyring-interface.md#decrypt-data-key
      //= type=implication
      //# If the encryption materials do contain a plaintext data key, OnDecrypt MUST NOT decrypt a data key.
      //# If the [decryption materials](structures.md#decryption-materials) do not include a plaintext data key,
      //# OnDecrypt MUST decrypt a data key.
      //# 
      //# The decrypt data key MUST modify the following fields in the [decryption materials](structures.md#decryption-materials):
      //# 
      //# - [Plaintext data key](structures.md#plaintext-data-key-1)
      //# 
      //# To perform this behavior, the keyring attempts to retrieve a plaintext data key from the input list
      //# of [encrypted data keys](structures.md#encrypted-data-key).
      //# 
      //# If the keyring is able to succesfully get at least one plaintext data key from any [encrypted data key](structures.md#encrypted-data-key)
      //# and the [decryption materials](structures.md#decryption-materials) still do not include a plaintext data key,
      //# it SHOULD set one resulting plaintext data key on the [decryption materials](structures.md#decryption-materials).
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          output.value.materials
        )
  }
}
