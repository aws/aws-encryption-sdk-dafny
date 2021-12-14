// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Keyring.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuites.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../StandardLibrary/Actions.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"
include "../../../Generated/AwsCryptographicMaterialProviders.dfy"

module
  {:extern "Dafny.Aws.Crypto.MaterialProviders.AwsKmsStrictKeyring"}
  MaterialProviders.AwsKmsStrictKeyring
{
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Seq
  import opened Actions
  import opened Constants
  import opened A = AwsKmsMrkMatchForDecrypt
  import Keyring
  import Materials
  import AlgorithmSuites
  import Aws.Crypto
  import opened KMSUtils
  import UTF8

  //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.5
  //= type=implication
  //# MUST implement the AWS Encryption SDK Keyring interface (../keyring-
  //# interface.md#interface)
  class AwsKmsStrictKeyring
    extends Keyring.VerifiableInterface
  {

    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const grantTokens: KMSUtils.GrantTokens

    constructor (
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MUST provide an AWS KMS SDK client
      // (blank line for duvet)
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      client: IAmazonKeyManagementService,
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MUST provide an AWS KMS key identifier
      awsKmsKey: string,
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.6
      //= type=implication
      //# *  MAY provide a list of Grant Tokens
      grantTokens: GrantTokens
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
      returns (res: Result<Crypto.OnEncryptOutput, string>)
      ensures res.Success?
      ==>
        && Materials.EncryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# If the input encryption materials (../structures.md#encryption-
      //# materials) do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling AWS KMS
      //# GenerateDataKey (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        && input.materials.plaintextDataKey.None?
      ==>
        GenerateDataKeyCalledWith(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
          //# configured AWS KMS client to make the call.
          client,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          GenerateDataKeyRequest(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "EncryptionContext" MUST be the encryption context
            //# (../structures.md#encryption-context) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            input.materials.encryptionContext,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "GrantTokens" MUST be this keyring's grant tokens
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/
            //# concepts.html#grant_token).
            grantTokens,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "KeyId" MUST be the keyring's KMS key identifier.
            awsKmsKey,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "NumberOfBytes" MUST be the key derivation input length
            //# (../algorithm-suites.md#key-derivation-input-length) specified by
            //# the algorithm suite (../algorithm-suites.md) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId).encrypt.keyLength as int32
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
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If the Generate Data Key call succeeds, OnEncrypt MUST verify that
        //# the response "Plaintext" length matches the specification of the
        //# algorithm suite (../algorithm-suites.md)'s Key Derivation Input
        //# Length field.
        && AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId).encrypt.keyLength as int == |res.value.materials.plaintextDataKey.value|
        && GenerateDataKeyResult(
            Last(res.value.materials.encryptedDataKeys).ciphertext,
            res.value.materials.plaintextDataKey.value
          )

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
      //= type=implication
      //# If the input encryption materials (../structures.md#encryption-
      //# materials) do contain a plaintext data key, OnEncrypt MUST attempt to
      //# encrypt the plaintext data key using the configured AWS KMS key
      //# identifier.
      ensures
        && input.materials.plaintextDataKey.Some?
      ==>
        && EncryptCalledWith(
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# The keyring MUST call AWS KMS Encrypt
          //# (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Encrypt.html) using the configured AWS KMS client.
          client,
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
          //= type=implication
          //# The keyring
          //# MUST AWS KMS Encrypt call with a request constructed as follows:
          EncryptRequest(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //# *  "EncryptionContext" MUST be the encryption context
            //# (../structures.md#encryption-context) included in the input
            //# encryption materials (../structures.md#encryption-materials).
            input.materials.encryptionContext,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //# *  "GrantTokens" MUST be this keyring's grant tokens
            //# (https://docs.aws.amazon.com/kms/latest/developerguide/
            //# concepts.html#grant_token).
            grantTokens,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "KeyId" MUST be the configured AWS KMS key identifier.
            awsKmsKey,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
            //= type=implication
            //# *  "PlaintextDataKey" MUST be the plaintext data key in the
            //# encryption materials (../structures.md#encryption-materials).
            input.materials.plaintextDataKey.value
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
        && EncryptResult(Last(res.value.materials.encryptedDataKeys).ciphertext)
    {
      var materials := input.materials;
      var suite := AlgorithmSuites.GetSuite(input.materials.algorithmSuiteId);
      if materials.plaintextDataKey.None? {
        var generatorRequest := GenerateDataKeyRequest(
          materials.encryptionContext,
          grantTokens,
          awsKmsKey,
          suite.encrypt.keyLength as int32
        );

        var maybeGenerateResponse := GenerateDataKey(client, generatorRequest);

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# If the call to AWS KMS GenerateDataKey
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html) does not succeed, OnEncrypt MUST NOT modify
        //# the encryption materials (../structures.md#encryption-materials) and
        //# MUST fail.
        if maybeGenerateResponse.Failure? {
          return Failure(maybeGenerateResponse.error);
        }
        var generateResponse := maybeGenerateResponse.value;

        :- Need(generateResponse.IsWellFormed(), "Invalid response from KMS GenerateDataKey");
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# The Generate Data Key response's "KeyId" MUST be a
        //# valid AWS KMS key ARN (aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Need(
          ParseAwsKmsIdentifier(generateResponse.keyID).Success?,
          "Invalid response from KMS GenerateDataKey:: Invalid Key Id"
        );
        :- Need(
          suite.encrypt.keyLength as int == |generateResponse.plaintext|,
          "Invalid response from AWS KMS GenerateDataKey: Invalid data key"
        );

        var providerInfo :- UTF8.Encode(generateResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, "AWS KMS Key ID too long.");

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
          ciphertext := generateResponse.ciphertextBlob
        );
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# *  MUST set the plaintext data key on the encryption materials
        //# (../structures.md#encryption-materials) as the response
        //# "Plaintext".
        var plaintextDataKey := generateResponse.plaintext;

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# *  MUST append a new encrypted data key (../structures.md#encrypted-
        //# data-key) to the encrypted data key list in the encryption
        //# materials (../structures.md#encryption-materials), constructed as
        //# follows:
        var result :- Materials.EncryptionMaterialAddDataKey(materials, plaintextDataKey, [edk]);
        return Success(Crypto.OnEncryptOutput(
          materials := result
        ));
      } else {
        var encryptRequest := KMSUtils.EncryptRequest(
          materials.encryptionContext,
          grantTokens,
          awsKmsKey,
          materials.plaintextDataKey.value
        );
        var maybeEncryptResponse := KMSUtils.Encrypt(client, encryptRequest);

        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //= type=implication
        //# If the call to AWS KMS Encrypt
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html) does not succeed, OnEncrypt MUST fail.
        if maybeEncryptResponse.Failure? {
          return Failure(maybeEncryptResponse.error);
        }

        var encryptResponse := maybeEncryptResponse.value;
        :- Need(encryptResponse.IsWellFormed(), "Invalid response from KMS Encrypt");
        //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.7
        //# If the Encrypt call succeeds the response's "KeyId" MUST be A valid
        //# AWS KMS key ARN (aws-kms-key-arn.md#a-valid-aws-kms-arn).
        :- Need(
          ParseAwsKmsIdentifier(encryptResponse.keyID).Success?,
          "Invalid response from AWS KMS Encrypt:: Invalid Key Id"
        );

        var providerInfo :- UTF8.Encode(encryptResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, "AWS KMS Key ID too long.");

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
          ciphertext := encryptResponse.ciphertextBlob
        );

        var result :- Materials.EncryptionMaterialAddEncryptedDataKeys(materials, [edk]);
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
      returns (res: Result<Crypto.OnDecryptOutput, string>)
      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //= type=implication
      //# If the decryption materials (../structures.md#decryption-materials)
      //# already contained a valid plaintext data key OnDecrypt MUST return an
      //# error.
      ensures input.materials.plaintextDataKey.Some? ==> res.Failure?
      ensures res.Success?
      ==>
        && Materials.DecryptionMaterialsTransitionIsValid(
          input.materials,
          res.value.materials
        )

      ensures
        && input.materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.materials.plaintextDataKey.Some?
        && exists edk | edk in input.encryptedDataKeys
        ::
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.keyProviderId == PROVIDER_ID
          && DecryptCalledWith(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# To attempt to decrypt a particular encrypted data key
            //# (../structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
            //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html) with the configured AWS KMS client.
            client,
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# When calling AWS KMS Decrypt
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            DecryptRequest(
              //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
              //= type=implication
              //# *  "KeyId" MUST be the configured AWS KMS key identifier.
              awsKmsKey,
              //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
              //= type=implication
              //# *  "CiphertextBlob" MUST be the encrypted data key ciphertext
              //# (../structures.md#ciphertext).
              edk.ciphertext,
              //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
              //= type=implication
              //# *  "EncryptionContext" MUST be the encryption context
              //# (../structures.md#encryption-context) included in the input
              //# decryption materials (../structures.md#decryption-materials).
              input.materials.encryptionContext,
              //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
              //= type=implication
              //# *  "GrantTokens" MUST be this keyring's grant tokens
              //# (https://docs.aws.amazon.com/kms/latest/developerguide/
              //# concepts.html#grant_token).
              grantTokens
            ))
          //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
          //= type=implication
          //# *  MUST immediately return the modified decryption materials
          //# (../structures.md#decryption-materials).
          && DecryptResult(
            //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
            //= type=implication
            //# *  The "KeyId" field in the response MUST equal the configured AWS
            //# KMS key identifier.
            awsKmsKey,
            res.value.materials.plaintextDataKey.value)
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

      :- Need(
        Materials.DecryptionMaterialsWithoutPlaintextDataKey(materials),
        "Keyring recieved decryption materials that already contain a plaintext data key.");

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsKey);
      var edksToAttempt :- FilterWithResult(filter, input.encryptedDataKeys);

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

      return match outcome {
        case Success(mat) =>
          assert exists edk | edk in edksToAttempt
          ::
            && edk in input.encryptedDataKeys
            && filter.Ensures(edk, Success(true))
            && decryptClosure.Ensures(edk, Success(mat))
            && DecryptCalledWith(
              client,
              DecryptRequest(
                awsKmsKey,
                edk.ciphertext,
                materials.encryptionContext,
                grantTokens
              ))
            && DecryptResult(awsKmsKey, mat.plaintextDataKey.value);
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
    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMSUtils.GrantTokens

    constructor(
      materials: Materials.DecryptionMaterialsPendingPlaintextDataKey,
      client: IAmazonKeyManagementService,
      awsKmsKey: AwsKmsIdentifierString,
      grantTokens: KMSUtils.GrantTokens
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
        && Materials.DecryptionMaterialsTransitionIsValid(materials, res.value)
        && DecryptCalledWith(
          client,
          DecryptRequest(
            awsKmsKey,
            edk.ciphertext,
            materials.encryptionContext,
            grantTokens
          )
        )
        && DecryptResult(awsKmsKey, res.value.plaintextDataKey.value)
    }

    method Invoke(
      edk: Crypto.EncryptedDataKey
    ) returns (res: Result<Materials.SealedDecryptionMaterials, string>)
      ensures Ensures(edk, res)
    {

      var decryptRequest := KMSUtils.DecryptRequest(
        awsKmsKey,
        edk.ciphertext,
        materials.encryptionContext,
        grantTokens
      );

      var decryptResponse :- KMSUtils.Decrypt(client, decryptRequest);
      :- Need(
        && decryptResponse.keyID == awsKmsKey
        && AlgorithmSuites.GetSuite(materials.algorithmSuiteId).encrypt.keyLength as int == |decryptResponse.plaintext|
        , "Invalid response from KMS Decrypt");

      //= compliance/framework/aws-kms/aws-kms-keyring.txt#2.8
      //# *  MUST set the plaintext data key on the decryption materials
      //# (../structures.md#decryption-materials) as the response
      //# "Plaintext".
      var result :- Materials.DecryptionMaterialsAddDataKey(materials, decryptResponse.plaintext);
      return Success(result);
    }
  }
}
