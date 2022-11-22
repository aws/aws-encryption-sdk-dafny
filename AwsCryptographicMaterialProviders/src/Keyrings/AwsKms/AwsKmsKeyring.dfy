// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "AwsKmsArnParsing.dfy"
include "AwsKmsUtils.dfy"

include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"

module AwsKmsKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AwsKmsUtils
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import Keyring
  import Materials
  import AlgorithmSuites
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = ComAmazonawsKmsTypes
  import UTF8

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#interface
  //= type=implication
  //# MUST implement the [AWS Encryption SDK Keyring interface](../keyring-interface.md#interface)
  class AwsKmsKeyring
    extends Keyring.VerifiableInterface
  {

    const client: KMS.IKeyManagementServiceClient
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const grantTokens: KMS.GrantTokenList

    predicate ValidState()
    ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && client.ValidState()
      && client.Modifies <= Modifies
      && History !in client.Modifies
    }

    constructor (
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS KMS SDK client
      // (blank line for duvet)
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      client: KMS.IKeyManagementServiceClient,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# - MUST provide an AWS KMS key identifier
      awsKmsKey: string,
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# - MAY provide a list of Grant Tokens
      grantTokens: KMS.GrantTokenList
    )
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# The AWS KMS
      //# key identifier MUST be [a valid identifier](aws-kms-key-arn.md#a-
      //# valid-aws-kms-identifier).
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#initialization
      //= type=implication
      //# The AWS KMS key identifier MUST NOT be null or empty.
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires client.ValidState()
      ensures
        && this.client      == client
        && this.awsKmsKey   == awsKmsKey
        && this.grantTokens == grantTokens
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - client.Modifies)
    {
      var parsedAwsKmsId    := ParseAwsKmsIdentifier(awsKmsKey);
      this.client      := client;
      this.awsKmsKey   := awsKmsKey;
      this.awsKmsArn   := parsedAwsKmsId.value;
      this.grantTokens := grantTokens;

      History := new Types.IKeyringCallHistory();
      Modifies := {History} + client.Modifies;
    }

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials]
    //# (../structures.md#encryption-materials) as input.
    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      ensures res.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          res.value.materials
        )

      ensures StringifyEncryptionContext(input.materials.encryptionContext).Failure?
      ==>
        res.Failure?

      ensures !KMS.IsValid_KeyIdType(awsKmsKey)
      ==>
        res.Failure?

      ensures
        && input.materials.plaintextDataKey.Some?
        && !KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
      ==>
        res.Failure?

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
      //= type=implication
      //# If the input [encryption materials](../structures.md#encryption-materials)
      //# do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling [AWS KMS
      //# GenerateDataKey](https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        // This must be before the .None? check, otherwise the verifier fails
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && input.materials.plaintextDataKey.None?
        && maybeStringifiedEncCtx.Success?
      ==>
        && 0 < |client.History.GenerateDataKey|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //= type=implication
        //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
        //# configured AWS KMS client to make the call.
        && Last(client.History.GenerateDataKey).input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          == KMS.GenerateDataKeyRequest(
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `EncryptionContext` MUST be the [encryption context]
            //# (../structures.md#encryption-context) included in the input
            //# [encryption materials](../structures.md#encryption-materials).
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `GrantTokens` MUST be this keyring's [grant tokens]
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
            GrantTokens := Some(grantTokens),
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `KeyId` MUST be the keyring's KMS key identifier.
            KeyId := awsKmsKey,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `NumberOfBytes` MUST be the [key derivation input length]
            //# (../algorithm-suites.md#key-derivation-input-length) specified by
            //# the [algorithm suite](../algorithm-suites.md) included in the input
            //# [encryption materials](../structures.md#encryption-materials).
            NumberOfBytes := Some(AlgorithmSuites.GetEncryptKeyLength(input.materials.algorithmSuite)),
            KeySpec := None
          )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
      //= type=implication
      //# - MUST output the modified [encryption materials]
      //# (../structures.md#encryption-materials)
      ensures
        && input.materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.materials.plaintextDataKey.Some?
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && KMS.IsValid_CiphertextType(Last(res.value.materials.encryptedDataKeys).ciphertext)
        && var algSuite := input.materials.algorithmSuite;
        && Last(client.History.GenerateDataKey).output.Success?
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //= type=implication
        //# If the Generate Data Key call succeeds, OnEncrypt MUST verify that
        //# the response `Plaintext` length matches the specification of the
        //# [algorithm suite](../algorithm-suites.md)'s Key Derivation Input
        //# Length field.
        && AlgorithmSuites.GetEncryptKeyLength(algSuite) as int == |res.value.materials.plaintextDataKey.value|
        && exists returnedKeyId
          ::
            && Last(client.History.GenerateDataKey).output.value
            == KMS.GenerateDataKeyResponse(
              KeyId := returnedKeyId,
              // The last data key is the one just added and what should be the result of the KMS call
              CiphertextBlob := Some(Last(res.value.materials.encryptedDataKeys).ciphertext),
              Plaintext := Some(res.value.materials.plaintextDataKey.value)
            )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
      //= type=implication
      //# If the input [encryption materials](../structures.md#encryption-
      //# materials) do contain a plaintext data key, OnEncrypt MUST attempt to
      //# encrypt the plaintext data key using the configured AWS KMS key
      //# identifier.
      ensures
        && input.materials.plaintextDataKey.Some?
        // These already-ensured clauses are required because we cannot depend on a res.Success? or res.Failure? to verify
        // that the client was called as it may be called on both paths
        && KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
      ==>
        && var stringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext).Extract();
        && 0 < |client.History.Encrypt|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //= type=implication
        //# The keyring MUST call [AWS KMS Encrypt]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_Encrypt.html) using the configured AWS KMS client.
        && Last(client.History.Encrypt).input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //= type=implication
          //# The keyring
          //# MUST AWS KMS Encrypt call with a request constructed as follows:
          == KMS.EncryptRequest(
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //# - `EncryptionContext` MUST be the [encryption context]
            //# (../structures.md#encryption-context) included in the input
            //# [encryption materials](../structures.md#encryption-materials).
            EncryptionContext := Some(stringifiedEncCtx),
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //# - `GrantTokens` MUST be this keyring's [grant tokens]
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
            GrantTokens := Some(grantTokens),
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `KeyId` MUST be the configured AWS KMS key identifier.
            KeyId := awsKmsKey,
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
            //= type=implication
            //# - `PlaintextDataKey` MUST be the plaintext data key in the
            //# [encryption materials](../structures.md#encryption-materials).
            Plaintext := input.materials.plaintextDataKey.value,
            EncryptionAlgorithm := None
          )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
      //= type=implication
      //# If all Encrypt calls succeed, OnEncrypt MUST output the modified
      //# [encryption materials](../structures.md#encryption-materials).
      ensures
        && input.materials.plaintextDataKey.Some?
        && res.Success?
      ==>
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //= type=implication
        //# If
        //# verified, OnEncrypt MUST append a new [encrypted data key]
        //# (../structures.md#encrypted-data-key) to the encrypted data key list
        //# in the [encryption materials](../structures.md#encryption-materials),
        //# constructed as follows:
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && KMS.IsValid_CiphertextType(Last(res.value.materials.encryptedDataKeys).ciphertext)
        && 0 < |client.History.Encrypt|
        && Last(client.History.Encrypt).output.Success?
        && exists returnedKeyId, returnedEncryptionAlgorithm
        ::
          && Last(client.History.Encrypt).output.value
          == KMS.EncryptResponse(
            CiphertextBlob := Some(Last(res.value.materials.encryptedDataKeys).ciphertext),
            KeyId := returnedKeyId,
            EncryptionAlgorithm := returnedEncryptionAlgorithm
          )
    {
      var materials := input.materials;
      var suite := input.materials.algorithmSuite;
      var stringifiedEncCtx :- StringifyEncryptionContext(input.materials.encryptionContext);

      if materials.plaintextDataKey.None? {
        var generatorRequest := KMS.GenerateDataKeyRequest(
          EncryptionContext := Some(stringifiedEncCtx),
          GrantTokens := Some(grantTokens),
          KeyId := awsKmsKey,
          NumberOfBytes := Some(AlgorithmSuites.GetEncryptKeyLength(suite)),
          KeySpec := None
        );

        var maybeGenerateResponse := client.GenerateDataKey(generatorRequest);

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //# If the call to [AWS KMS GenerateDataKey]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKey.html)
        //# does not succeed, OnEncrypt MUST NOT modify
        //# the [encryption materials](../structures.md#encryption-materials) and
        //# MUST fail.
        var generateResponse :- maybeGenerateResponse
          .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //# The Generate Data Key response’s `KeyId` MUST be [a
        //# valid AWS KMS key ARN](aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Need(
          && generateResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(generateResponse.KeyId.value).Success?,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from KMS GenerateDataKey:: Invalid Key Id")
        );
        :- Need(
          && generateResponse.Plaintext.Some?
          && AlgorithmSuites.GetEncryptKeyLength(suite) as nat == |generateResponse.Plaintext.value|,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from AWS KMS GenerateDataKey: Invalid data key")
        );

        var providerInfo :- UTF8.Encode(generateResponse.KeyId.value).MapFailure(WrapStringToError);
        :- Need(|providerInfo| < UINT16_LIMIT,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from AWS KMS GenerateDataKey: Key ID too long."));

        :- Need(
          && generateResponse.CiphertextBlob.Some?
          && KMS.IsValid_CiphertextType(generateResponse.CiphertextBlob.value),
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from AWS KMS GeneratedDataKey: Invalid ciphertext")
        );

        var edk := Types.EncryptedDataKey(
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - the [key provider id](../structures.md#key-provider-id) MUST be
          //# "aws-kms".
          keyProviderId := PROVIDER_ID,
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - the [key provider information](../structures.md#key-provider-
          //# information) MUST be the response `KeyId`.
          keyProviderInfo := providerInfo,
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - the [ciphertext](../structures.md#ciphertext) MUST be the
          //# response `CiphertextBlob`.
          ciphertext := generateResponse.CiphertextBlob.value
        );
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //# - MUST set the plaintext data key on the [encryption materials]
        //# (../structures.md#encryption-materials) as the response
        //# `Plaintext`.
        var plaintextDataKey := generateResponse.Plaintext.value;

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //# - MUST append a new [encrypted data key](../structures.md#encrypted-
        //# data-key) to the encrypted data key list in the [encryption
        //# materials](../structures.md#encryption-materials), constructed as
        //# follows:
        var result :- Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk]);
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      } else {
        :- Need(KMS.IsValid_PlaintextType(materials.plaintextDataKey.value),
          Types.AwsCryptographicMaterialProvidersException(
            message := "PlaintextDataKey is invalid"));

        var encryptRequest := KMS.EncryptRequest(
          EncryptionContext := Some(stringifiedEncCtx),
          GrantTokens := Some(grantTokens),
          KeyId := awsKmsKey,
          Plaintext := materials.plaintextDataKey.value,
          EncryptionAlgorithm := None
        );
        var maybeEncryptResponse := client.Encrypt(encryptRequest);

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //= type=implication
        //# If the call to [AWS KMS Encrypt]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_Encrypt.html)
        //# does not succeed, OnEncrypt MUST fail.
        var encryptResponse :- maybeEncryptResponse
          .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
        //# If the Encrypt call succeeds the response’s `KeyId` MUST be
        //# [A valid AWS KMS key ARN](aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Need(
          && encryptResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(encryptResponse.KeyId.value).Success?,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from AWS KMS Encrypt:: Invalid Key Id")
        );

        var providerInfo :- UTF8.Encode(encryptResponse.KeyId.value)
          .MapFailure(WrapStringToError);
        :- Need(|providerInfo| < UINT16_LIMIT,
          Types.AwsCryptographicMaterialProvidersException(
            message := "AWS KMS Key ID too long."));

        :- Need(encryptResponse.CiphertextBlob.Some?,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Invalid response from AWS KMS Encrypt: Invalid Ciphertext Blob")
        );

        var edk := Types.EncryptedDataKey(
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - The [key provider id](../structures.md#key-provider-id) MUST be
          //# "aws-kms".
          keyProviderId := PROVIDER_ID,
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - The [key provider information](../structures.md#key-provider-information)
          //# MUST be the response `KeyId`.  Note that the `KeyId`
          //# in the response is always in key ARN format.
          keyProviderInfo := providerInfo,
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#onencrypt
          //# - The [ciphertext](../structures.md#ciphertext) MUST be the response
          //# `CiphertextBlob`.
          ciphertext := encryptResponse.CiphertextBlob.value
        );

        var result :- Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
        return Success(Types.OnEncryptOutput(
          materials := result
        ));
      }
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
    //= type=implication
    //# OnDecrypt MUST take [decryption materials]
    //# (../structures.md#decryption-materials) and a list of [encrypted data
    //# keys](../structures.md#encrypted-data-key) as input.
    method OnDecrypt'(
      input: Types.OnDecryptInput
    )
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //= type=implication
      //# If the [decryption materials](../structures.md#decryption-materials)
      //# already contained a valid plaintext data key OnDecrypt MUST return an
      //# error.
      ensures input.materials.plaintextDataKey.Some? ==> res.Failure?

      ensures
        && res.Success?
      ==>
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.Decrypt|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
        //= type=implication
        //# - The length of the response’s `Plaintext` MUST equal the
        //# [key derivation input length](../algorithm-suites.md#key-derivation-input-length)
        //# specified by the [algorithm suite](../algorithm-suites.md)
        //# included in the input [decryption materials]
        //# (../structures.md#decryption-materials).
        && AlgorithmSuites.GetEncryptKeyLength(input.materials.algorithmSuite) as nat == |res.value.materials.plaintextDataKey.value|
        && var LastDecrypt := Last(client.History.Decrypt);
        && LastDecrypt.output.Success?
        && exists edk
        // , returnedEncryptionAlgorithm
        | edk in input.encryptedDataKeys
        ::
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
          //= type=implication
          //# - Its provider ID MUST exactly match the value “aws-kms”.
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
          //= type=implication
          //# When calling [AWS KMS Decrypt]
          //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_Decrypt.html),
          //# the keyring MUST call with a request constructed
          //# as follows:
          && KMS.DecryptRequest(
              //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
              //= type=implication
              //# - `KeyId` MUST be the configured AWS KMS key identifier.
              KeyId := Some(awsKmsKey),
              //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
              //= type=implication
              //# - `CiphertextBlob` MUST be the [encrypted data key ciphertext]
              //# (../structures.md#ciphertext).
              CiphertextBlob := edk.ciphertext,
              //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
              //= type=implication
              //# - `EncryptionContext` MUST be the [encryption context]
              //# (../structures.md#encryption-context) included in the input
              //# [decryption materials](../structures.md#decryption-materials).
              EncryptionContext := Some(maybeStringifiedEncCtx.value),
              //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
              //= type=implication
              //# - `GrantTokens` MUST be this keyring's [grant tokens]
              //# (https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
              GrantTokens := Some(grantTokens),
              EncryptionAlgorithm := None
            )
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
            //= type=implication
            //# To attempt to decrypt a particular [encrypted data key]
            //# (../structures.md#encrypted-data-key), OnDecrypt MUST call [AWS KMS
            //# Decrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_Decrypt.html)
            //# with the configured AWS KMS client.
            == LastDecrypt.input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
          //= type=implication
          //# - The `KeyId` field in the response MUST equal the configured AWS
          //# KMS key identifier.
          && LastDecrypt.output.value.KeyId == Some(awsKmsKey)
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
          //= type=implication
          //# - MUST immediately return the modified [decryption materials]
          //# (../structures.md#decryption-materials).
          && LastDecrypt.output.value.Plaintext == res.value.materials.plaintextDataKey
    {

      var materials := input.materials;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException(
          message := "Keyring received decryption materials that already contain a plaintext data key."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# The set of encrypted data keys MUST first be filtered to match this
      //#  keyring’s configuration.
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsKey);
      var edksToAttempt :- FilterWithResult(filter, input.encryptedDataKeys);

      :- Need(0 < |edksToAttempt|,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unable to decrypt data key: No Encrypted Data Keys found to match."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# For each encrypted data key in the filtered set, one at a time, the
      //# OnDecrypt MUST attempt to decrypt the data key.
      //# If this attempt
      //# results in an error, then these errors MUST be collected.
      var decryptClosure := new DecryptSingleEncryptedDataKey(
        materials,
        client,
        awsKmsKey,
        grantTokens
      );

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# If the response does not satisfies these requirements then an error
      //# MUST be collected and the next encrypted data key in the filtered set
      //# MUST be attempted.
      var outcome, attempts := ReduceToSuccess(
        decryptClosure,
        edksToAttempt
      );

      var SealedDecryptionMaterials :- outcome
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
        //# If OnDecrypt fails to successfully decrypt any [encrypted data key]
        //# (../structures.md#encrypted-data-key), then it MUST yield an error
        //# that includes all the collected errors.
        .MapFailure(errors => Types.Collection( list := errors));

      assert decryptClosure.Ensures(Last(attempts).input, Success(SealedDecryptionMaterials), DropLast(attempts));
      return Success(Types.OnDecryptOutput(
        materials := SealedDecryptionMaterials
      ));
    }
  }

  class OnDecryptEncryptedDataKeyFilter
    extends DeterministicActionWithResult<Types.EncryptedDataKey, bool, Types.Error>
  {
    const awsKmsKey: AwsKmsIdentifierString

    constructor(awsKmsKey: AwsKmsIdentifierString) {
      this.awsKmsKey := awsKmsKey;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<bool, Types.Error>
    ) {
      && (
          && res.Success?
          && res.value
        ==>
          edk.keyProviderId == PROVIDER_ID)
    }

    method Invoke(edk: Types.EncryptedDataKey)
      returns (res: Result<bool, Types.Error>)
      ensures Ensures(edk, res)
    {

      if edk.keyProviderId != PROVIDER_ID {
        return Success(false);
      }

      if !UTF8.ValidUTF8Seq(edk.keyProviderInfo) {
        // The Keyring produces UTF8 keyProviderInfo.
        // If an `aws-kms` encrypted data key's keyProviderInfo is not UTF8
        // this is an error, not simply an EDK to filter out.
        return Failure(Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid AWS KMS encoding, provider info is not UTF8."));
      }

      var keyId :- UTF8.Decode(edk.keyProviderInfo).MapFailure(WrapStringToError);
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# - The provider info MUST be a [valid AWS KMS ARN](aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of `key` or
      //# OnDecrypt MUST fail.
      var _ :- ParseAwsKmsArn(keyId).MapFailure(WrapStringToError);

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# - The provider info MUST match the configured AWS KMS key
      //# identifier.
      return Success(this.awsKmsKey == keyId);
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      Types.EncryptedDataKey,
      Materials.SealedDecryptionMaterials,
      Types.Error>
  {
    const materials: Materials.DecryptionMaterialsPendingPlaintextDataKey
    const client: KMS.IKeyManagementServiceClient
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMS.GrantTokenList

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: KMS.IKeyManagementServiceClient,
      awsKmsKey: AwsKmsIdentifierString,
      grantTokens: KMS.GrantTokenList
    )
      requires client.ValidState()
      ensures
      && this.materials == materials
      && this.client == client
      && this.awsKmsKey == awsKmsKey
      && this.grantTokens == grantTokens
      ensures Invariant()
    {
      this.materials := materials;
      this.client := client;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
      Modifies := client.Modifies;
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      && client.ValidState()
      && client.Modifies == Modifies
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<Materials.SealedDecryptionMaterials, Types.Error>,
      attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
        res.Success?
      ==>
        && Invariant()
        && KMS.IsValid_CiphertextType(edk.ciphertext)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.Decrypt|
        && KMS.DecryptRequest(
          KeyId := Some(awsKmsKey),
          CiphertextBlob := edk.ciphertext,
          EncryptionContext := Some(maybeStringifiedEncCtx.value),
          GrantTokens := Some(grantTokens),
          EncryptionAlgorithm := None
        ) == Last(client.History.Decrypt).input
        && Last(client.History.Decrypt).output.Success?
        && Last(client.History.Decrypt).output.value.Plaintext.Some?
        && Last(client.History.Decrypt).output.value.Plaintext
          == res.value.plaintextDataKey
        && Last(client.History.Decrypt).output.value.KeyId == Some(awsKmsKey)
    }

    method Invoke(
      edk: Types.EncryptedDataKey,
      ghost attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    ) returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(edk, res, attemptsState)
    {
      :- Need(KMS.IsValid_CiphertextType(edk.ciphertext),
        Types.AwsCryptographicMaterialProvidersException( message := "Ciphertext length invalid"));

      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);
      var decryptRequest := KMS.DecryptRequest(
        KeyId := Some(awsKmsKey),
        CiphertextBlob := edk.ciphertext,
        EncryptionContext := Some(stringifiedEncCtx),
        GrantTokens := Some(grantTokens),
        EncryptionAlgorithm := None
      );

      var maybeDecryptResponse := client.Decrypt(decryptRequest);
      var decryptResponse :- maybeDecryptResponse
        .MapFailure(e => Types.ComAmazonawsKms( ComAmazonawsKms := e ));

      :- Need(
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && AlgorithmSuites.GetEncryptKeyLength(materials.algorithmSuite) as nat == |decryptResponse.Plaintext.value|
        , Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid response from KMS Decrypt"));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-keyring.md#ondecrypt
      //# - MUST set the plaintext data key on the [decryption materials]
      //# (../structures.md#decryption-materials) as the response
      //# `Plaintext`.
      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value);
      return Success(result);
    }
  }

}
