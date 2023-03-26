// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


include "../../../Model/AwsCryptographyMaterialProvidersTypes.dfy"
include "Constants.dfy"
include "../../AwsArnParsing.dfy"
include "AwsKmsUtils.dfy"
include "AwsKmsKeyring.dfy"
include "../../KeyWrapping/EdkWrapping.dfy"
include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"

module AwsKmsMrkKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import opened AwsKmsKeyring
  import Types = AwsCryptographyMaterialProvidersTypes
  import KMS = Types.ComAmazonawsKmsTypes
  import opened Seq
  import opened Actions
  import opened Constants
  import Keyring
  import Materials
  import AlgorithmSuites
  import UTF8
  import EdkWrapping
  import MaterialWrapping

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

      ensures StringifyEncryptionContext(input.materials.encryptionContext).Failure?
      ==>
        output.Failure?
      
      ensures !KMS.IsValid_KeyIdType(awsKmsKey)
      ==>
        output.Failure?

      ensures
        && input.materials.plaintextDataKey.Some?
        && !KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
      ==>
        output.Failure?

      // TODO: add ensures for pdk.none & intermediateKeyWrapping response
      //       add ensures for pdk.some & intermediateKeyWrapping request and response

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the input [encryption materials](../structures.md#encryption-
      //# materials) do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling [AWS KMS
      //# GenerateDataKey](https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        && output.Success?
        // TODO update specification to clarify expectations around when Generate vs Encrypt is called
        && input.materials.plaintextDataKey.None?
        && input.materials.algorithmSuite.edkWrapping.IntermediateKeyWrapping?
      ==>
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.GenerateDataKey|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
        //# configured AWS KMS client to make the call.
        && Last(client.History.GenerateDataKey).input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          == KMS.GenerateDataKeyRequest(
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            GrantTokens := Some(grantTokens),
            KeyId := awsKmsKey,
            NumberOfBytes := Some(AlgorithmSuites.GetEncryptKeyLength(input.materials.algorithmSuite)),
            KeySpec := None
          )

      ensures
        && output.Success?
        && input.materials.plaintextDataKey.None?
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
      ==>
        && var suite := input.materials.algorithmSuite;
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.GenerateDataKey|
        && Last(client.History.GenerateDataKey).input
          == KMS.GenerateDataKeyRequest(
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            GrantTokens := Some(grantTokens),
            KeyId := awsKmsKey,
            NumberOfBytes := Some(AlgorithmSuites.GetEncryptKeyLength(suite)),
            KeySpec := None
          )
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# -  OnEncrypt MUST output the modified [encryption materials]
      //# (../structures.md#encryption-materials) 
      ensures
        && output.Success?
        && input.materials.plaintextDataKey.None?
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
      ==>
        && Last(client.History.GenerateDataKey).output.Success?
        && var GenerateResponse := Last(client.History.GenerateDataKey).output.value;
        && GenerateResponse.CiphertextBlob.Some?
        && GenerateResponse.KeyId.Some?
        && UTF8.Encode(GenerateResponse.KeyId.value).Success?
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# If verified, OnEncrypt MUST do the following with the response
        //# from [AWS KMS GenerateDataKey]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html):
        && |output.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && KMS.IsValid_CiphertextType(Last(output.value.materials.encryptedDataKeys).ciphertext)
        && Last(output.value.materials.encryptedDataKeys).ciphertext 
          == GenerateResponse.CiphertextBlob.value
        && Last(output.value.materials.encryptedDataKeys).keyProviderInfo
          == UTF8.Encode(GenerateResponse.KeyId.value).value
        && 0 < |client.History.GenerateDataKey|
        && exists returnedKeyId, kmsPlaintext
          ::
            && Last(client.History.GenerateDataKey).output.value
              == KMS.GenerateDataKeyResponse(
                KeyId := Some(returnedKeyId),
                CiphertextBlob := Some(Last(output.value.materials.encryptedDataKeys).ciphertext),
                Plaintext := kmsPlaintext
              )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the input [encryption materials](../structures.md#encryption-
      //# materials) do contain a plaintext data key, OnEncrypt MUST attempt to
      //# encrypt the plaintext data key using the configured AWS KMS key
      //# identifier.
      ensures
        && output.Success?
        && input.materials.plaintextDataKey.Some?
        // TODO clarify spec expectations around calling Generate vs Encrypt
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
      ==>
        && KMS.IsValid_PlaintextType(input.materials.plaintextDataKey.value)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.Encrypt|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
        //= type=implication
        //# The keyring MUST call [AWS KMS Encrypt]
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_Encrypt.html) using the configured AWS KMS client.
        && Last(client.History.Encrypt).input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
          //= type=implication
          //# The keyring
          //# MUST AWS KMS Encrypt call with a request constructed as follows:
          == KMS.EncryptRequest(
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            GrantTokens := Some(grantTokens),
            KeyId := awsKmsKey,
            Plaintext := input.materials.plaintextDataKey.value,
            EncryptionAlgorithm := None
          )

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If all Encrypt calls succeed, OnEncrypt MUST output the modified
      //# [encryption materials](../structures.md#encryption-materials).
      ensures
        && input.materials.plaintextDataKey.Some?
        && output.Success?
        // TODO clarify spec expectations around calling Generate vs Encrypt
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
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
        && KMS.IsValid_CiphertextType(Last(output.value.materials.encryptedDataKeys).ciphertext)
        && 0 < |client.History.Encrypt|
        && Last(client.History.Encrypt).output.Success?
        && exists returnedKeyId, returnedEncryptionAlgorithm
        ::
          && Last(client.History.Encrypt).output.value
          == KMS.EncryptResponse(
            CiphertextBlob := Some(Last(output.value.materials.encryptedDataKeys).ciphertext),
            KeyId := returnedKeyId,
            EncryptionAlgorithm := returnedEncryptionAlgorithm
          )
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the call to [AWS KMS Encrypt]
      //# (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_Encrypt.html) does not succeed, OnEncrypt MUST fail.
      ensures
        && input.materials.plaintextDataKey.Some?
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
        && |client.History.Encrypt| == |old(client.History.Encrypt)| + 1
        && Last(client.History.Encrypt).output.Failure?
      ==>
        output.Failure?
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //= type=implication
      //# If the call to [AWS KMS GenerateDataKey]
      //# (https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKey.html) does not succeed,
      //# OnEncrypt MUST NOT modify the [encryption materials]
      //# (../structures.md#encryption-materials) and MUST fail. 
      ensures
        && input.materials.plaintextDataKey.None?
        && input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
        && StringifyEncryptionContext(input.materials.encryptionContext).Success?
        && |client.History.GenerateDataKey| == |old(client.History.GenerateDataKey)| + 1
        && Last(client.History.GenerateDataKey).output.Failure?
      ==>
        output.Failure?
    {

      var materials := input.materials;
      var suite := input.materials.algorithmSuite;
      var stringifiedEncCtx :- StringifyEncryptionContext(input.materials.encryptionContext);
      
      // If kmsGenerateAndWrap is invoked and succeeds it ensures that the 
      // response'd KeyId is a valid AWS KMS key Arn.

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //# The Generate Data Key response’s `KeyId` MUST be [A valid AWS
      //# KMS key ARN](aws-kms-key-arn.md#identifying-an-aws-kms-
      //# multi-region-key).
      var kmsGenerateAndWrap := new KmsGenerateAndWrapKeyMaterial(
        client,
        awsKmsKey,
        grantTokens
      );

      // If kmsWrap is invoked and succeeds it ensures that the 
      // response'd KeyId is a valid AWS KMS key Arn.

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //# If the Encrypt call succeeds the response’s `KeyId` MUST be [A valid
      //# AWS KMS key ARN](aws-kms-key-arn.md#a-valid-aws-kms-arn).
      var kmsWrap := new KmsWrapKeyMaterial(
        client,
        awsKmsKey,
        grantTokens
      );
      
      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#onencrypt
      //# If the Generate Data Key call succeeds, OnEncrypt MUST 
      //# verify that the response `Plaintext` length matches the specification 
      //# of the [algorithm suite](../algorithm-suites.md)'s Key Derivation Input Length field. 
      var wrapOutput :- EdkWrapping.WrapEdkMaterial<KmsWrapInfo>(
        encryptionMaterials := materials,
        wrap := kmsWrap,
        generateAndWrap := kmsGenerateAndWrap
      );
      
      var kmsKeyArn := wrapOutput.wrapInfo.kmsKeyArn;
      var symmetricSigningKeyList :=
        if wrapOutput.symmetricSigningKey.Some? then
          Some([wrapOutput.symmetricSigningKey.value])
        else
          None;
      
      var providerInfo :- UTF8.Encode(kmsKeyArn).MapFailure(WrapStringToError);
      :- Need(|providerInfo| < UINT16_LIMIT,
        Types.AwsCryptographicMaterialProvidersException(
          message := "Invalid response from AWS KMS GenerateDataKey: Key ID too long."));
      
      var edk := Types.EncryptedDataKey(
        keyProviderId := PROVIDER_ID,
        keyProviderInfo := providerInfo,
        ciphertext := wrapOutput.wrappedMaterial
      );      

      if (wrapOutput.GenerateAndWrapEdkMaterialOutput?) {
        // Wrapped new pdk. Add pdk and first edk to materials.
        assert |client.History.GenerateDataKey| > 0 && Last(client.History.GenerateDataKey).output.Success?;
        assert |kmsGenerateAndWrap.client.History.GenerateDataKey| > 0 &&
          Last(kmsGenerateAndWrap.client.History.GenerateDataKey).output.Success?; 
        assert Last(client.History.GenerateDataKey).output.value == Last(kmsGenerateAndWrap.client.History.GenerateDataKey).output.value;
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
        && 0 < |client.History.Decrypt|
        //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
        //= type=implication
        //# - The length of the response’s `Plaintext` MUST equal the [key
        //# derivation input length](../algorithm-suites.md#key-derivation-
        //# input-length) specified by the [algorithm suite](../algorithm-
        //# suites.md) included in the input [decryption materials]
        //# (../structures.md#decryption-materials).
        && var suite := input.materials.algorithmSuite;
        && AlgorithmSuites.GetEncryptKeyLength(suite) as nat == |output.value.materials.plaintextDataKey.value|
        && var LastDecrypt := Last(client.History.Decrypt);
        && LastDecrypt.output.Success?

        && exists edk | edk in input.encryptedDataKeys
        ::
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# -  Its provider ID MUST exactly match the value “aws-kms”.
          && var maybeWrappedMaterial :=
              EdkWrapping.GetProviderWrappedMaterial(edk.ciphertext, input.materials.algorithmSuite);
          && maybeWrappedMaterial.Success?
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(maybeWrappedMaterial.value)
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# When calling [AWS KMS Decrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_Decrypt.html),
          //# the keyring MUST call with a request constructed as follows: 
          && KMS.DecryptRequest(
              KeyId := Some(awsKmsKey),
              CiphertextBlob := maybeWrappedMaterial.value,
              EncryptionContext := Some(maybeStringifiedEncCtx.value),
              GrantTokens := Some(grantTokens),
              EncryptionAlgorithm := None
            )
            //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
            //= type=implication
            //# To attempt to decrypt a particular [encrypted data key]
            //# (../structures.md#encrypted-data-key), OnDecrypt MUST call [AWS KMS
            //# Decrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_Decrypt.html)
            //# with the configured AWS KMS client.
            == LastDecrypt.input
          //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
          //= type=implication
          //# - The `KeyId` field in the response MUST equal the configured AWS
          //# KMS key identifier.
          && LastDecrypt.output.value.KeyId == Some(awsKmsKey)
          && (
              input.materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING?
            ==>
              LastDecrypt.output.value.Plaintext == output.value.materials.plaintextDataKey)
      
    {
      var materials := input.materials;
      var suite := input.materials.algorithmSuite;

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        Types.AwsCryptographicMaterialProvidersException( message := "Keyring received decryption materials that already contain a plaintext data key."));

      //= aws-encryption-sdk-specification/framework/aws-kms/aws-kms-mrk-keyring.md#ondecrypt
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring’s configuration.
      var filter := new AwsKmsUtils.OnDecryptMrkAwareEncryptedDataKeyFilter(awsKmsArn, PROVIDER_ID);
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
        && var maybeProviderWrappedMaterial :=
            EdkWrapping.GetProviderWrappedMaterial(edk.ciphertext, materials.algorithmSuite);
        && maybeProviderWrappedMaterial.Success?
        && KMS.IsValid_CiphertextType(maybeProviderWrappedMaterial.value)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && 0 < |client.History.Decrypt|
        && KMS.DecryptRequest(
          KeyId := Some(awsKmsKey),
          CiphertextBlob := maybeProviderWrappedMaterial.value,
          EncryptionContext := Some(maybeStringifiedEncCtx.value),
          GrantTokens := Some(grantTokens),
          EncryptionAlgorithm := None
        ) == Last(client.History.Decrypt).input
        && Last(client.History.Decrypt).output.Success?
        && Last(client.History.Decrypt).output.value.Plaintext.Some?
        && (
          materials.algorithmSuite.edkWrapping.DIRECT_KEY_WRAPPING? ==>
            Last(client.History.Decrypt).output.value.Plaintext
              == res.value.plaintextDataKey)
        && Last(client.History.Decrypt).output.value.KeyId == Some(awsKmsKey)
      )
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
      var kmsUnwrap := new KmsUnwrapKeyMaterial(
        client,
        awsKmsKey,
        grantTokens
      );

      var unwrapOutputRes := EdkWrapping.UnwrapEdkMaterial(
        edk.ciphertext,
        materials,
        kmsUnwrap
      );
      var unwrapOutput :- unwrapOutputRes;

      var result :- Materials.DecryptionMaterialsAddDataKey(materials, unwrapOutput.plaintextDataKey, unwrapOutput.symmetricSigningKey);

      return Success(result);
    }
  }

}
