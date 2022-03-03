// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../StandardLibrary/Actions.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "AwsKmsArnParsing.dfy"

include "../../../Generated/AwsCryptographicMaterialProviders.dfy"
include "../../../Generated/KeyManagementService.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.AwsKmsKeyring"}
  MaterialProviders.AwsKmsKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import KMS = Com.Amazonaws.Kms
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import Keyring
  import Materials
  import AlgorithmSuites
  import Aws.Crypto
  import UTF8

  //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.5
  //= type=implication
  //# MUST implement the AWS Encryption SDK Keyring interface (../keyring-
  //# interface.md#interface)
  class AwsKmsKeyring
    extends Keyring.VerifiableInterface
  {

    const client: KMS.IKeyManagementServiceClient
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const grantTokens: KMS.GrantTokenList

    constructor (
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MUST provide an AWS KMS SDK client
      // (blank line for duvet)
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      client: KMS.IKeyManagementServiceClient,
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MUST provide an AWS KMS key identifier
      awsKmsKey: string,
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MAY provide a list of Grant Tokens
      grantTokens: KMS.GrantTokenList
    )
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS
      //# key identifier MUST be a valid identifier (aws-kms-key-arn.md#a-
      //# valid-aws-kms-identifier).
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS key identifier MUST NOT be null or empty.
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      ensures
        && this.client      == client
        && this.awsKmsKey   == awsKmsKey
        && this.grantTokens == grantTokens
    {
      var parsedAwsKmsId    := ParseAwsKmsIdentifier(awsKmsKey);
      this.client      := client;
      this.awsKmsKey   := awsKmsKey;
      this.awsKmsArn   := parsedAwsKmsId.value;
      this.grantTokens := grantTokens;
    }

    //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
    //= type=implication
    //# OnEncrypt MUST take encryption materials
    //# (../structures.md#encryption-materials) as input.
    method OnEncrypt(input: Crypto.OnEncryptInput)
      returns (res: Result<Crypto.OnEncryptOutput, Crypto.IAwsCryptographicMaterialProvidersException>)
      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
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

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# If the input encryption materials (../structures.md#encryption-
      //# materials) do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling AWS KMS
      //# GenerateDataKey (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        // This must be before the .None? check, otherwise the verifier fails
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && input.materials.plaintextDataKey.None?
        && maybeStringifiedEncCtx.Success?
      ==>
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
        //# configured AWS KMS client to make the call.
        client.GenerateDataKeyCalledWith(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          KMS.GenerateDataKeyRequest(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "EncryptionContext" MUST be the encryption context
            //# (../structures.md#encryption-context) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "GrantTokens" MUST be this keyring's grant tokens
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/
            //# concepts.html#grant_token).
            GrantTokens := Some(grantTokens),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "KeyId" MUST be the keyring's KMS key identifier.
            KeyId := awsKmsKey,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "NumberOfBytes" MUST be the key derivation input length
            //# (../algorithm-suites.md#key-derivation-input-length) specified by
            //# the algorithm suite (../algorithm-suites.md) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            NumberOfBytes := Some(AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId).encrypt.keyLength as int32),
            KeySpec := None
          ))

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# *  MUST output the modified encryption materials
      //# (../structures.md#encryption-materials)
      ensures
        && input.materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.materials.plaintextDataKey.Some?
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && KMS.IsValid_CiphertextType(Last(res.value.materials.encryptedDataKeys).ciphertext)
        && var algSuite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If the Generate Data Key call succeeds, OnEncrypt MUST verify that
        //# the response "Plaintext" length matches the specification of the
        //# algorithm suite (../algorithm-suites.md)'s Key Derivation Input
        //# Length field.
        && algSuite.encrypt.keyLength as int == |res.value.materials.plaintextDataKey.value|
        && exists returnedKeyId ::
          client.GenerateDataKeySucceededWith(
            input := KMS.GenerateDataKeyRequest(
              KeyId := awsKmsKey,
              EncryptionContext := Some(StringifyEncryptionContext(input.materials.encryptionContext).Extract()),
              GrantTokens := Some(grantTokens),
              NumberOfBytes := Some(algSuite.encrypt.keyLength as int32),
              KeySpec := None
            ),
            output := KMS.GenerateDataKeyResponse(
              KeyId := returnedKeyId,
              // The last data key is the one just added and what should be the result of the KMS call
              CiphertextBlob := Some(Last(res.value.materials.encryptedDataKeys).ciphertext),
              Plaintext := Some(res.value.materials.plaintextDataKey.value)
            )
          )

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# If the input encryption materials (../structures.md#encryption-
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
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# The keyring MUST call AWS KMS Encrypt
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html) using the configured AWS KMS client.
        && client.EncryptCalledWith(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# The keyring
          //# MUST AWS KMS Encrypt call with a request constructed as follows:
          KMS.EncryptRequest(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //# *  "EncryptionContext" MUST be the encryption context
            //# (../structures.md#encryption-context) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            EncryptionContext := Some(stringifiedEncCtx),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //# *  "GrantTokens" MUST be this keyring's grant tokens
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/
            //# concepts.html#grant_token).
            GrantTokens := Some(grantTokens),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "KeyId" MUST be the configured AWS KMS key identifier.
            KeyId := awsKmsKey,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "PlaintextDataKey" MUST be the plaintext data key in the
            //# encryption materials (../structures.md#encryption-materials).
            Plaintext := input.materials.plaintextDataKey.value,
            EncryptionAlgorithm := None
          ))

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# If all Encrypt calls succeed, OnEncrypt MUST output the modified
      //# encryption materials (../structures.md#encryption-materials).
      ensures
        && input.materials.plaintextDataKey.Some?
        && res.Success?
      ==>
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If
        //# verified, OnEncrypt MUST append a new encrypted data key
        //# (../structures.md#encrypted-data-key) to the encrypted data key list
        //# in the encryption materials (../structures.md#encryption-materials),
        //# constructed as follows:
        && |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1
        && KMS.IsValid_CiphertextType(Last(res.value.materials.encryptedDataKeys).ciphertext)
        && exists returnedKeyId, returnedEncryptionAlgorithm ::
          client.EncryptSucceededWith(
            input := KMS.EncryptRequest(
              KeyId := awsKmsKey,
              Plaintext := input.materials.plaintextDataKey.value,
              EncryptionContext := Some(StringifyEncryptionContext(input.materials.encryptionContext).Extract()),
              GrantTokens := Some(grantTokens),
              EncryptionAlgorithm := None
            ),
            output := KMS.EncryptResponse(
              CiphertextBlob := Some(Last(res.value.materials.encryptedDataKeys).ciphertext),
              KeyId := returnedKeyId,
              EncryptionAlgorithm := returnedEncryptionAlgorithm
            )
          )
    {
      var materials := input.materials;
      var suite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);
      var stringifiedEncCtxResult := StringifyEncryptionContext(input.materials.encryptionContext);
      var stringifiedEncCtx :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(
        stringifiedEncCtxResult);

      if materials.plaintextDataKey.None? {
        var generatorRequest := KMS.GenerateDataKeyRequest(
          EncryptionContext := Some(stringifiedEncCtx),
          GrantTokens := Some(grantTokens),
          KeyId := awsKmsKey,
          NumberOfBytes := Some(suite.encrypt.keyLength as int32),
          KeySpec := None
        );

        var maybeGenerateResponse := client.GenerateDataKey(generatorRequest);

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# If the call to AWS KMS GenerateDataKey
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html) does not succeed, OnEncrypt MUST NOT modify
        //# the encryption materials (../structures.md#encryption-materials) and
        //# MUST fail.
        if maybeGenerateResponse.Failure? {
          var errMsg := KMS.CastKeyManagementServiceErrorToString(maybeGenerateResponse.error);
          var exception := new Crypto.AwsCryptographicMaterialProvidersClientException(errMsg);
          return Failure(exception);
        }
        var generateResponse := maybeGenerateResponse.value;

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# The Generate Data Key response's "KeyId" MUST be a
        //# valid AWS KMS key ARN (aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Crypto.Need(
          && generateResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(generateResponse.KeyId.value).Success?,
          "Invalid response from KMS GenerateDataKey:: Invalid Key Id"
        );
        :- Crypto.Need(
          && generateResponse.Plaintext.Some?
          && suite.encrypt.keyLength as int == |generateResponse.Plaintext.value|,
          "Invalid response from AWS KMS GenerateDataKey: Invalid data key"
        );

        var providerInfoResult := UTF8.Encode(generateResponse.KeyId.value);
        var providerInfo :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(providerInfoResult);
        :- Crypto.Need(|providerInfo| < UINT16_LIMIT, "Invalid response from AWS KMS GenerateDataKey: Key ID too long.");

        :- Crypto.Need(
          && generateResponse.CiphertextBlob.Some?
          && KMS.IsValid_CiphertextType(generateResponse.CiphertextBlob.value),
          "Invalid response from AWS KMS GeneratedDataKey: Invalid ciphertext"
        );

        var edk := Crypto.EncryptedDataKey(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# -  the key provider id (../structures.md#key-provider-id) MUST be
          //# "aws-kms".
          keyProviderId := PROVIDER_ID,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# -  the key provider information (../structures.md#key-provider-
          //# information) MUST be the response "KeyId".
          keyProviderInfo := providerInfo,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# -  the ciphertext (../structures.md#ciphertext) MUST be the
          //# response "CiphertextBlob".
          ciphertext := generateResponse.CiphertextBlob.value
        );
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# *  MUST set the plaintext data key on the encryption materials
        //# (../structures.md#encryption-materials) as the response
        //# "Plaintext".
        var plaintextDataKey := generateResponse.Plaintext.value;

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# *  MUST append a new encrypted data key (../structures.md#encrypted-
        //# data-key) to the encrypted data key list in the encryption
        //# materials (../structures.md#encryption-materials), constructed as
        //# follows:
        var addKeyResult := Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk]);
        var result :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(addKeyResult);
        return Success(Crypto.OnEncryptOutput(
          materials := result
        ));
      } else {
        :- Crypto.Need(KMS.IsValid_PlaintextType(materials.plaintextDataKey.value), "PlaintextDataKey is invalid");

        var encryptRequest := KMS.EncryptRequest(
          EncryptionContext := Some(stringifiedEncCtx),
          GrantTokens := Some(grantTokens),
          KeyId := awsKmsKey,
          Plaintext := materials.plaintextDataKey.value,
          EncryptionAlgorithm := None
        );
        var maybeEncryptResponse := client.Encrypt(encryptRequest);

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If the call to AWS KMS Encrypt
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html) does not succeed, OnEncrypt MUST fail.
        if maybeEncryptResponse.Failure? {
          var errMsg := KMS.CastKeyManagementServiceErrorToString(maybeEncryptResponse.error);
          var exception := new Crypto.AwsCryptographicMaterialProvidersClientException(errMsg);
          return Failure(exception);
        }

        var encryptResponse := maybeEncryptResponse.value;

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# If the Encrypt call succeeds the response's "KeyId" MUST be A valid
        //# AWS KMS key ARN (aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Crypto.Need(
          && encryptResponse.KeyId.Some?
          && ParseAwsKmsIdentifier(encryptResponse.KeyId.value).Success?,
          "Invalid response from AWS KMS Encrypt:: Invalid Key Id"
        );

        var providerInfoResult := UTF8.Encode(encryptResponse.KeyId.value);
        var providerInfo :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(providerInfoResult);
        :- Crypto.Need(|providerInfo| < UINT16_LIMIT, "AWS KMS Key ID too long.");

        :- Crypto.Need(encryptResponse.CiphertextBlob.Some?,
          "Invalid response from AWS KMS Encrypt: Invalid Ciphertext Blob"
        );

        var edk := Crypto.EncryptedDataKey(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# *  The key provider id (../structures.md#key-provider-id) MUST be
          //# "aws-kms".
          keyProviderId := PROVIDER_ID,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# *  The key provider information (../structures.md#key-provider-
          //# information) MUST be the response "KeyId".  Note that the "KeyId"
          //# in the response is always in key ARN format.
          keyProviderInfo := providerInfo,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //# *  The ciphertext (../structures.md#ciphertext) MUST be the response
          //# "CiphertextBlob".
          ciphertext := encryptResponse.CiphertextBlob.value
        );

        var addKeyResult := Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
        var result :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(addKeyResult);
        return Success(Crypto.OnEncryptOutput(
          materials := result
        ));
      }
    }

    //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
    //= type=implication
    //# OnDecrypt MUST take decryption materials
    //# (../structures.md#decryption-materials) and a list of encrypted data
    //# keys (../structures.md#encrypted-data-key) as input.
    method OnDecrypt(
      input: Crypto.OnDecryptInput
    )
      returns (res: Result<Crypto.OnDecryptOutput, Crypto.IAwsCryptographicMaterialProvidersException>)
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //= type=implication
      //# If the decryption materials (../structures.md#decryption-materials)
      //# already contained a valid plaintext data key OnDecrypt MUST return an
      //# error.
      ensures input.materials.plaintextDataKey.Some? ==> res.Failure?

      ensures
        && res.Success?
      ==>
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(input.materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && exists edk | edk in input.encryptedDataKeys
        ::
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.keyProviderId == PROVIDER_ID
          && KMS.IsValid_CiphertextType(edk.ciphertext)
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# When calling AWS KMS Decrypt
          //# (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html), the keyring MUST call with a request constructed
          //# as follows:
          && var request := KMS.DecryptRequest(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  "KeyId" MUST be the configured AWS KMS key identifier.
            KeyId := Some(awsKmsKey),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  "CiphertextBlob" MUST be the encrypted data key ciphertext
            //# (../structures.md#ciphertext).
            CiphertextBlob := edk.ciphertext,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  "EncryptionContext" MUST be the encryption context
            //# (../structures.md#encryption-context) included in the input
            //# decryption materials (../structures.md#decryption-materials).
            EncryptionContext := Some(maybeStringifiedEncCtx.value),
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  "GrantTokens" MUST be this keyring's grant tokens
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/
            //# concepts.html#grant_token).
            GrantTokens := Some(grantTokens),
            EncryptionAlgorithm := None
          );
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# To attempt to decrypt a particular encrypted data key
          //# (../structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
          //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Decrypt.html) with the configured AWS KMS client.
          && client.DecryptCalledWith(request)
          && exists returnedEncryptionAlgorithm ::
            && var response := KMS.DecryptResponse(
              //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
              //= type=implication
              //# *  The "KeyId" field in the response MUST equal the configured AWS
              //# KMS key identifier.
              KeyId := Some(awsKmsKey),
              Plaintext := res.value.materials.plaintextDataKey,
              EncryptionAlgorithm := returnedEncryptionAlgorithm
            );
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  MUST immediately return the modified decryption materials
            //# (../structures.md#decryption-materials).
            && client.DecryptSucceededWith(request, response)
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# *  The length of the response's "Plaintext" MUST equal the key
          //# derivation input length (../algorithm-suites.md#key-derivation-
          //# input-length) specified by the algorithm suite (../algorithm-
          //# suites.md) included in the input decryption materials
          //# (../structures.md#decryption-materials).
          && AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId).encrypt.keyLength as int == |res.value.materials.plaintextDataKey.value|
    {

      var materials := input.materials;
      var suite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);

      :- Crypto.Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        "Keyring recieved decryption materials that already contain a plaintext data key.");

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsKey);
      var filterResult := FilterWithResult(filter, input.encryptedDataKeys);
      var edksToAttempt :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(filterResult);

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
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

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# If the response does not satisfies these requirements then an error
      //# MUST be collected and the next encrypted data key in the filtered set
      //# MUST be attempted.
      var outcome := ReduceToSuccess(
        decryptClosure,
        edksToAttempt
      );

      var stringifiedEncCtxResult := StringifyEncryptionContext(materials.encryptionContext);
      ghost var stringifiedEncCtx :- Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(
        stringifiedEncCtxResult);
      var result := match outcome {
        case Success(mat) =>
          assert exists edk | edk in edksToAttempt
          ::
            && edk in input.encryptedDataKeys
            && filter.Ensures(edk, Success(true))
            && decryptClosure.Ensures(edk, Success(mat));
          Success(Crypto.OnDecryptOutput(
            materials := mat
          ))
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
        //# If OnDecrypt fails to successfully decrypt any encrypted data key
        //# (../structures.md#encrypted-data-key), then it MUST yield an error
        //# that includes all the collected errors.
        case Failure(errors) =>
          if |errors| == 0 then
            Failure("Unable to decrypt data key: No Encrypted Data Keys found to match.")
          else
            var concatString := (s, a) => a + "\n" + s;
            var error := Seq.FoldRight(
              concatString,
              errors,
              "Unable to decrypt data key:\n"
            );
            Failure(error)
      };
      var wrapped := Crypto.AwsCryptographicMaterialProvidersClientException.WrapResultString(result);
      return wrapped;
    }
  }

  class OnDecryptEncryptedDataKeyFilter
    extends ActionWithResult<Crypto.EncryptedDataKey, bool, string>
  {
    const awsKmsKey: AwsKmsIdentifierString

    constructor(awsKmsKey: AwsKmsIdentifierString) {
      this.awsKmsKey := awsKmsKey;
    }

    predicate Ensures(
      edk: Crypto.EncryptedDataKey,
      res: Result<bool, string>
    ) {
      && (
          && res.Success?
          && res.value
        ==>
          edk.keyProviderId == PROVIDER_ID)
    }

    method Invoke(edk: Crypto.EncryptedDataKey)
      returns (res: Result<bool, string>)
      ensures Ensures(edk, res)
    {

      if edk.keyProviderId != PROVIDER_ID {
        return Success(false);
      }

      if !UTF8.ValidUTF8Seq(edk.keyProviderInfo) {
        // The Keyring produces UTF8 keyProviderInfo.
        // If an `aws-kms` encrypted data key's keyProviderInfo is not UTF8
        // this is an error, not simply an EDK to filter out.
        return Failure("Invalid AWS KMS encoding, provider info is not UTF8.");
      }

      var keyId :- UTF8.Decode(edk.keyProviderInfo);
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
      //# OnDecrypt MUST fail.
      var _ :- ParseAwsKmsArn(keyId);

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# *  The provider info MUST match the configured AWS KMS key
      //# identifier.
      return Success(this.awsKmsKey == keyId);
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      Crypto.EncryptedDataKey,
      Materials.SealedDecryptionMaterials,
      string>
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
      ensures
      && this.materials == materials
      && this.client == client
      && this.awsKmsKey == awsKmsKey
      && this.grantTokens == grantTokens
    {
      this.materials := materials;
      this.client := client;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
    }

    predicate Ensures(
      edk: Crypto.EncryptedDataKey,
      res: Result<Materials.SealedDecryptionMaterials, string>
    ) {
        res.Success?
      ==>
        && KMS.IsValid_CiphertextType(edk.ciphertext)
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && var maybeStringifiedEncCtx := StringifyEncryptionContext(materials.encryptionContext);
        && maybeStringifiedEncCtx.Success?
        && var request := KMS.DecryptRequest(
          KeyId := Some(awsKmsKey),
          CiphertextBlob := edk.ciphertext,
          EncryptionContext := Some(maybeStringifiedEncCtx.value),
          GrantTokens := Some(grantTokens),
          EncryptionAlgorithm := None
        );
        && client.DecryptCalledWith(request)
        && exists returnedEncryptionAlgorithm ::
          && var response := KMS.DecryptResponse(
            KeyId := Some(awsKmsKey),
            Plaintext := Some(res.value.plaintextDataKey.value),
            EncryptionAlgorithm := returnedEncryptionAlgorithm
          );
          && client.DecryptSucceededWith(request, response)
    }

    method Invoke(
      edk: Crypto.EncryptedDataKey
    ) returns (res: Result<Materials.SealedDecryptionMaterials, string>)
      ensures Ensures(edk, res)
    {
      :- Need(KMS.IsValid_CiphertextType(edk.ciphertext), "Ciphertext length invalid");

      var stringifiedEncCtx :- StringifyEncryptionContext(materials.encryptionContext);
      var decryptRequest := KMS.DecryptRequest(
        KeyId := Some(awsKmsKey),
        CiphertextBlob := edk.ciphertext,
        EncryptionContext := Some(stringifiedEncCtx),
        GrantTokens := Some(grantTokens),
        EncryptionAlgorithm := None
      );

      var maybeDecryptResponse := client.Decrypt(decryptRequest);
      if maybeDecryptResponse.Failure? {
        return Failure(KMS.CastKeyManagementServiceErrorToString(maybeDecryptResponse.error));
      }

      var decryptResponse := maybeDecryptResponse.value;
      :- Need(
        && decryptResponse.KeyId.Some?
        && decryptResponse.KeyId.value == awsKmsKey
        && decryptResponse.Plaintext.Some?
        && AlgorithmSuites.GetSuite(materials.algorithmSuiteId).encrypt.keyLength as int == |decryptResponse.Plaintext.value|
        , "Invalid response from KMS Decrypt");

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# *  MUST set the plaintext data key on the decryption materials
      //# (../structures.md#decryption-materials) as the response
      //# "Plaintext".
      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.Plaintext.value);
      return Success(result);
    }
  }

  // TODO: copied from AwsKmsMrkAwareSymmetricKeyring
  // TODO use ValidUTF8Bytes everywhere in business logic, so that this (and usages in implementation/preconditions) can be removed
  function method StringifyEncryptionContext(utf8EncCtx: Crypto.EncryptionContext):
    (res: Result<KMS.EncryptionContextType, string>)
  {
    if |utf8EncCtx| == 0 then Success(map[])
    else
      var stringifyResults: map<UTF8.ValidUTF8Bytes, Result<(string, string), string>> :=
        map utf8Key | utf8Key in utf8EncCtx.Keys :: utf8Key := StringifyEncryptionContextPair(utf8Key, utf8EncCtx[utf8Key]);
      if exists r | r in stringifyResults.Values :: r.Failure?
        then Failure("Encryption context contains invalid UTF8")
      else
        assert forall r | r in stringifyResults.Values :: r.Success?;
        // TODO state that UTF8.Decode is injective so we don't need this
        var stringKeysUnique := forall k, k' | k in stringifyResults && k' in stringifyResults
          :: k != k' ==> stringifyResults[k].value.0 != stringifyResults[k'].value.0;
        if !stringKeysUnique then Failure("Encryption context keys are not unique")  // this should never happen...
        else Success(map r | r in stringifyResults.Values :: r.value.0 := r.value.1)
  }

  function method StringifyEncryptionContextPair(utf8Key: UTF8.ValidUTF8Bytes, utf8Value: UTF8.ValidUTF8Bytes):
    (res: Result<(string, string), string>)
    ensures (UTF8.Decode(utf8Key).Success? && UTF8.Decode(utf8Value).Success?) <==> res.Success?
  {
    var decodedKey := UTF8.Decode(utf8Key);
    var decodedValue := UTF8.Decode(utf8Value);
    if (decodedKey.Failure?) then Failure(decodedKey.error)
    else if (decodedValue.Failure?) then Failure(decodedValue.error)
    else Success((decodedKey.value, decodedValue.value))
  }
}
