// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsUtils.dfy"
include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"

module AwsKmsMrkKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
   import opened AwsArnParsing
  import opened AwsKmsUtils
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = Types.ComAmazonawsKmsTypes
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import Keyring
  import Materials
  import AlgorithmSuites
  import UTF8

  //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#interface
  //= type=implication
  //# MUST implement the [AWS Encryption SDK Keyring interface](../keyring-interface.md#interface)
  class AwsKmsMrkKeyring
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
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#initialization
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      client: KMS.IKeyManagementServiceClient,
      awsKmsKey: string,
      grantTokens: KMS.GrantTokenList
    )
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#initialization
      //= type=implication
      //# The AWS KMS key identifier MUST NOT be null or empty.
      //# The AWS KMS
      //# key identifier MUST be [a valid identifier](aws-kms-key-arn.md#a-
      //# valid-aws-kms-identifier).
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires client.ValidState()
      ensures
        && this.client      == client
        && this.awsKmsKey   == awsKmsKey
        && this.grantTokens == grantTokens
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies - client.Modifies)
    {
      var parsedAwsKmsId  := ParseAwsKmsIdentifier(awsKmsKey);
      this.client         := client;
      this.awsKmsKey      := awsKmsKey;
      this.awsKmsArn      := parsedAwsKmsId.value;
      this.grantTokens    := grantTokens;

      History := new Types.IKeyringCallHistory();
      Modifies := {History} + client.Modifies;
    }

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
    //= type=implication
    //# OnEncrypt MUST take [encryption materials](../structures.md#encryption-
    //# materials) as input.
    method {:vcs_split_on_every_assert} OnEncrypt'(input: Types.OnEncryptInput)
      returns (output: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures unchanged(History)
      ensures OnEncryptEnsuresPublicly(input, output)
      ensures output.Success?
      ==>
        && Materials.ValidEncryptionMaterialsTransition(
          input.materials,
          output.value.materials
        )
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the input [encryption materials](../structures.md#encryption-
      //# materials) do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling [AWS KMS
      //# GenerateDataKey](https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        && input.materials.plaintextDataKey.None?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
      ==>
        0 < |client.History.GenerateDataKey|

      ensures
        var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && input.materials.plaintextDataKey.None?
        && KMS.IsValid_KeyIdType(awsKmsKey)
        && maybeStringifiedEncCtx.Success?
      ==> (
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          && var GenerateDataKeyRequest := KMS.GenerateDataKeyRequest(
            KeyId := awsKmsKey,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            NumberOfBytes := Option.Some(AlgorithmSuites.GetEncryptKeyLength(input.materials.algorithmSuite)),
            KeySpec := Option.None
          );
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
        //# configured AWS KMS client to make the call.
        && GenerateDataKeyRequest == Last(client.History.GenerateDataKey).input
      )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# -  OnEncrypt MUST output the modified [encryption materials]
      //# (../structures.md#encryption-materials)
      ensures
        && input.materials.plaintextDataKey.None?
        && output.Success?
      ==>
        && Last(client.History.GenerateDataKey).output.Success?
        && output.value.materials.plaintextDataKey.Some?
        && |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && var suite := input.materials.algorithmSuite;
        && var GenerateDataKeyResponse := Last(client.History.GenerateDataKey).output.value;
        && GenerateDataKeyResponse.Plaintext.Some?
        && GenerateDataKeyResponse.CiphertextBlob.Some?
        && GenerateDataKeyResponse.KeyId.Some?
        && UTF8.Encode(GenerateDataKeyResponse.KeyId.value).Success?
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If the Generate Data Key call succeeds, OnEncrypt MUST verify that
        //# the response `Plaintext` length matches the specification of the
        //# [algorithm suite](../algorithm-suites.md)'s Key Derivation Input Length
        //# field.
        && AlgorithmSuites.GetEncryptKeyLength(suite) as int == |GenerateDataKeyResponse.Plaintext.value|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If verified, OnEncrypt MUST do the following with the response
        //# from [AWS KMS GenerateDataKey]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html):
        && Last(output.value.materials.encryptedDataKeys).ciphertext
          == GenerateDataKeyResponse.CiphertextBlob.value
        && output.value.materials.plaintextDataKey.value
          == GenerateDataKeyResponse.Plaintext.value
        && Last(output.value.materials.encryptedDataKeys).keyProviderInfo
          == UTF8.Encode(GenerateDataKeyResponse.KeyId.value).value

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //# If the call to[AWS KMS GenerateDataKey]
      //# (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html) does not succeed, OnEncrypt MUST NOT modify
      //# the [encryption materials](../structures.md#encryption-materials) and
      //# MUST fail.
      ensures
        && input.materials.plaintextDataKey.None?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
        && |client.History.GenerateDataKey| == |old(client.History.GenerateDataKey)| + 1
        && Last(client.History.GenerateDataKey).output.Failure?
      ==>
        output.Failure?

      ensures
        && input.materials.plaintextDataKey.Some?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
        && KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
      ==>
        |client.History.Encrypt| == |old(client.History.Encrypt)| + 1

      ensures
        var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && input.materials.plaintextDataKey.Some?
        && KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
        && maybeStringifiedEncCtx.Success?
      ==>
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# The keyring MUST call [AWS KMS Encrypt]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html) using the configured AWS KMS client.      
        && |client.History.Encrypt| == |old(client.History.Encrypt)| + 1
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# The keyring
        //# MUST AWS KMS Encrypt call with a request constructed as follows:
        && var EncryptRequest := KMS.EncryptRequest(
          KeyId := awsKmsKey,
          Plaintext := input.materials.plaintextDataKey.value,
          EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
          GrantTokens := Option.Some(grantTokens),
          EncryptionAlgorithm := Option.None
        );
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If the input [encryption materials](../structures.md#encryption-
        //# materials) do contain a plaintext data key, OnEncrypt MUST attempt to
        //# encrypt the plaintext data key using the configured AWS KMS key
        //# identifier.
        && EncryptRequest == Last(client.History.Encrypt).input

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If all Encrypt calls succeed, OnEncrypt MUST output the modified
      //# [encryption materials](../structures.md#encryption-materials).
      ensures
        && input.materials.plaintextDataKey.Some?
        && KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
        && output.Success?
      ==>
        && Last(client.History.Encrypt).output.Success?
        && var EncryptResponse := Last(client.History.Encrypt).output.value;
        && EncryptResponse.CiphertextBlob.Some?
        && EncryptResponse.KeyId.Some?
        && UTF8.Encode(EncryptResponse.KeyId.value).Success?
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If verified, OnEncrypt MUST do the following with the
        //# response from [AWS KMS Encrypt]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html):
        && |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && Last(output.value.materials.encryptedDataKeys).ciphertext
          == EncryptResponse.CiphertextBlob.value
        && Last(output.value.materials.encryptedDataKeys).keyProviderInfo
          == UTF8.Encode(EncryptResponse.KeyId.value).value

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the call to [AWS KMS Encrypt]
      //# (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_Encrypt.html) does not succeed, OnEncrypt MUST fail.
      ensures
        && input.materials.plaintextDataKey.Some?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
        && |client.History.Encrypt| == |old(client.History.Encrypt)| + 1
        && Last(client.History.Encrypt).output.Failure?
      ==>
        output.Failure?
    {

      var materials := input.materials;
      var suite := input.materials.algorithmSuite;
      var stringifiedEncCtx :- StringifyEncryptionContext(input.materials.encryptionContext);
      if materials.plaintextDataKey.None? {

        var generatorRequest := KMS.GenerateDataKeyRequest(
          KeyId := awsKmsKey,
          EncryptionContext := Option.Some(stringifiedEncCtx),
          GrantTokens := Option.Some(grantTokens),
          NumberOfBytes := Option.Some(AlgorithmSuites.GetEncryptKeyLength(suite)),
          KeySpec := Option.None
        );

        var maybeGenerateResponse := client.GenerateDataKey(generatorRequest);

        var generateResponse :- maybeGenerateResponse
          .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //# The Generate Data Key response’s `KeyId` MUST be [A valid AWS
        //# KMS key ARN](aws-kms-key-arn.md#identifying-an-aws-kms-
        //# multi-region-key).
        :- Need(
          && generateResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(generateResponse.KeyId.value).Success?,
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from KMS GenerateDataKey: Invalid Key Id")
        );
        var keyId := generateResponse.KeyId.value;
        var providerInfo :- UTF8.Encode(keyId).MapFailure(WrapStringToError);
        :- Need(|providerInfo| < UINT16_LIMIT,
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from KMS GenerateDataKey: AWS KMS Key ID too long."));

        :- Need(
          && generateResponse.Plaintext.Some?
          && AlgorithmSuites.GetEncryptKeyLength(suite) as nat == |generateResponse.Plaintext.value|,
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from KMS GenerateDataKey: Invalid data key")
        );
        var plaintextDataKey := generateResponse.Plaintext.value;

        :- Need(
          && generateResponse.CiphertextBlob.Some?
          && KMS.IsValid_CiphertextType(generateResponse.CiphertextBlob.value),
          Types.AwsCryptographicMaterialProvidersException( message := "Returned ciphertext is invalid length"));
        var ciphertext :- assert generateResponse.CiphertextBlob;

        var edk := Types.EncryptedDataKey(
          keyProviderId := PROVIDER_ID,
          keyProviderInfo := providerInfo,
          ciphertext := ciphertext
        );

        // TODO add support
        :- Need(materials.algorithmSuite.symmetricSignature.None?,
          Types.AwsCryptographicMaterialProvidersException(
            message := "Symmetric Signatures not yet implemented."));

        var outputMaterials :- Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk], None);
        var result := Types.OnEncryptOutput(
          materials := outputMaterials
        );
        return Success(result);
      } else {
        :- Need(KMS.IsValid_PlaintextType(materials.plaintextDataKey.value),
          Types.AwsCryptographicMaterialProvidersException( message := "PlaintextDataKey is invalid length")
        );
        var encryptRequest := KMS.EncryptRequest(
            KeyId := awsKmsKey,
            Plaintext := materials.plaintextDataKey.value,
            EncryptionContext := Option.Some(stringifiedEncCtx),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None
        );
        var maybeEncryptResponse := client.Encrypt(encryptRequest);

        var encryptResponse :- maybeEncryptResponse
          .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //# If the Encrypt call succeeds the response’s `KeyId` MUST be [A valid
        //# AWS KMS key ARN](aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Need(
          && encryptResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(encryptResponse.KeyId.value).Success?,
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from AWS KMS Encrypt: Invalid Key Id")
        );

        :- Need(encryptResponse.CiphertextBlob.Some?,
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from AWS KMS Encrypt: Invalid Ciphertext Blob")
        );

        var providerInfo :- UTF8
          .Encode(encryptResponse.KeyId.Extract())
          .MapFailure(WrapStringToError);
        :- Need(|providerInfo| < UINT16_LIMIT,
          Types.AwsCryptographicMaterialProvidersException( message := "AWS KMS Key ID too long."));

        var edk := Types.EncryptedDataKey(
          keyProviderId := PROVIDER_ID,
          keyProviderInfo := providerInfo,
          ciphertext := encryptResponse.CiphertextBlob.value
        );

        var outputMaterials :- Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk], None);
        var result := Types.OnEncryptOutput(
          materials := outputMaterials
        );
        return Success(result);
      }
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}

    //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
    //= type=implication
    //# OnDecrypt MUST take [decryption materials](../structures.md#decryption-
    //# materials) and a list of [encrypted data keys]
    //# (../structures.md#encrypted-data-key) as input.
    method OnDecrypt'(
      input: Types.OnDecryptInput
    )
      returns (output: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures unchanged(History)
      ensures OnDecryptEnsuresPublicly(input, output)
      ensures output.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          output.value.materials
        )

      ensures
        && input.materials.plaintextDataKey.None?
        && output.Success?
      ==>
        && output.value.materials.plaintextDataKey.Some?
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
        //= type=implication
        //# - The length of the response’s `Plaintext` MUST equal the [key
        //# derivation input length](../algorithm-suites.md#key-derivation-
        //# input-length) specified by the [algorithm suite](../algorithm-
        //# suites.md) included in the input [decryption materials]
        //# (../structures.md#decryption-materials).
        && var suite := input.materials.algorithmSuite;
        && AlgorithmSuites.GetEncryptKeyLength(suite) as nat == |output.value.materials.plaintextDataKey.value|
        && 0 < |client.History.Decrypt|

        && exists edk | edk in input.encryptedDataKeys
        ::
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# -  Its provider ID MUST exactly match the value “aws-kms”.
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          && Last(client.History.Decrypt).output.Success?
          && KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob :=  edk.ciphertext,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
          ) == Last(client.History.Decrypt).input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# To attempt to decrypt a particular [encrypted data key]
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call [AWS KMS
          //# Decrypt](https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.

            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
            //= type=implication
            //# When calling [AWS KMS Decrypt]
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
          && var DecryptResponse := Last(client.History.Decrypt).output.value;
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# If the response does satisfies these requirements then OnDecrypt MUST
          //# do the following with the response:
          && output.value.materials.plaintextDataKey == DecryptResponse.Plaintext



    {
      var materials := input.materials;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException( message := "Keyring received decryption materials that already contain a plaintext data key."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring’s configuration.
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsArn);
      var edksToAttempt :- FilterWithResult(filter, input.encryptedDataKeys);

      :- Need(0 < |edksToAttempt|,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Unable to decrypt data key: No Encrypted Data Keys found to match."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# For each encrypted data key in the filtered set, one at a time, the
      //# OnDecrypt MUST attempt to decrypt the data key.
      //# If this attempt
      //# results in an error, then these errors MUST be collected.
      var decryptClosure: DecryptSingleEncryptedDataKey := new DecryptSingleEncryptedDataKey(
        materials,
        client,
        awsKmsKey,
        grantTokens
      );

      // assert client.Modifies <= Modifies;
      // assert decryptClosure.Modifies <= Modifies;
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# If the response does not satisfies these requirements then an error
      //# MUST be collected and the next encrypted data key in the filtered set
      //# MUST be attempted.
      var outcome, attempts := ReduceToSuccess(
        decryptClosure,
        edksToAttempt
      );

      var SealedDecryptionMaterials :- outcome
        .MapFailure(errors => Types.CollectionOfErrors( list := errors));

      assert decryptClosure.Ensures(Last(attempts).input, Success(SealedDecryptionMaterials), DropLast(attempts));

      return Success(Types.OnDecryptOutput(
        materials := SealedDecryptionMaterials
      ));
    }
  }

  class OnDecryptEncryptedDataKeyFilter
    extends DeterministicActionWithResult<Types.EncryptedDataKey, bool, Types.Error>
  {
    const awsKmsKey: AwsKmsIdentifier
    function Modifies(): set<object> {{}}

    constructor(awsKmsKey: AwsKmsIdentifier) {
      this.awsKmsKey := awsKmsKey;
    }

    predicate Ensures(
      edk: Types.EncryptedDataKey,
      res: Result<bool, Types.Error>
    )
    {
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
        return Failure(
          Types.AwsCryptographicMaterialProvidersException( message := "Invalid AWS KMS encoding, provider info is not UTF8."));
      }

      var keyId :- UTF8
        .Decode(edk.keyProviderInfo)
        .MapFailure(WrapStringToError);
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# -  The provider info MUST be a [valid AWS KMS ARN](aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of `key` or
      //# OnDecrypt MUST fail.
      var arn :- ParseAwsKmsArn(keyId).MapFailure(WrapStringToError);

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# -  The the function [AWS KMS MRK Match for Decrypt](aws-kms-mrk-match-
      //# for-decrypt.md#implementation) called with the configured AWS KMS
      //# key identifier and the provider info MUST return `true`.
      return Success(AwsKmsMrkMatchForDecrypt(
        awsKmsKey,
        AwsKmsArnIdentifier(arn)
      ));
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
      attempts : seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      reads Modifies
      decreases Modifies
    {
      && (res.Success?
      ==>
        && Invariant()
        && KMS.IsValid_CiphertextType(edk.ciphertext)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.Decrypt|
        && KMS.DecryptRequest(
            KeyId := Option.Some(awsKmsKey),
            CiphertextBlob :=  edk.ciphertext,
            EncryptionContext := Option.Some(maybeStringifiedEncCtx.Extract()),
            GrantTokens := Option.Some(grantTokens),
            EncryptionAlgorithm := Option.None()
        ) == Last(client.History.Decrypt).input
        && Last(client.History.Decrypt).output.Success?
        && Last(client.History.Decrypt).output.value.Plaintext.Some?
        && Last(client.History.Decrypt).output.value.Plaintext
          == res.value.plaintextDataKey
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value))
    }

    method Invoke(
      edk: Types.EncryptedDataKey,
      ghost attemptsState: seq<ActionInvoke<Types.EncryptedDataKey, Result<Materials.SealedDecryptionMaterials, Types.Error>>>
    )
      returns (res: Result<Materials.SealedDecryptionMaterials, Types.Error>)
      requires Invariant()
      decreases Modifies
      modifies Modifies
      ensures Invariant()
      ensures Ensures(edk, res, attemptsState)
    {
      :- Need(KMS.IsValid_CiphertextType(edk.ciphertext),
        Types.AwsCryptographicMaterialProvidersException( message := "Ciphertext length invalid"));
      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);
      var decryptRequest := KMS.DecryptRequest(
        KeyId := Option.Some(awsKmsKey),
        CiphertextBlob := edk.ciphertext,
        EncryptionContext := Option.Some(stringifiedEncCtx),
        GrantTokens := Option.Some(grantTokens),
        EncryptionAlgorithm := Option.None()
      );

      var maybeDecryptResponse := client.Decrypt(decryptRequest);
      var decryptResponse :- maybeDecryptResponse
        .MapFailure(e => Types.ComAmazonawsKms( ComAmazonawsKms := e ));
      var suite := materials.algorithmSuite;
      :- Need(
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && AlgorithmSuites.GetEncryptKeyLength(suite) as nat == |decryptResponse.Plaintext.value|
        , Types.AwsCryptographicMaterialProvidersException( message := "Invalid response from KMS Decrypt"));
      
      // TODO add support
      :- Need(materials.algorithmSuite.symmetricSignature.None?,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Symmetric Signatures not yet implemented."));

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value, None);
      return Success(result);
    }
  }

}
