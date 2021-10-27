// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Defs.dfy"
include "../../Materials.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../StandardLibrary/Actions.dfy"
include "Constants.dfy"
include "AwsKmsMrkMatchForDecrypt.dfy"

module {:extern "AwsKmsMrkAwareSymmetricKeyring"} AwsKmsMrkAwareSymmetricKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Seq
  import opened Actions
  import opened Constants
  import opened M = AwsKmsMrkMatchForDecrypt
  import opened KeyringDefs
  import Materials
  import opened KMSUtils
  import UTF8

  //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.5
  //= type=implication
  //# MUST implement the AWS Encryption SDK Keyring interface (../keyring-
  //# interface.md#interface)
  class AwsKmsMrkAwareSymmetricKeyring
    extends Keyring
  {

    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const grantTokens: KMSUtils.GrantTokens

    constructor (
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS SDK client MUST NOT be null.
      client: IAmazonKeyManagementService,
      awsKmsKey: string,
      grantTokens: GrantTokens
    )
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.6
      //= type=implication
      //# The AWS KMS key identifier MUST NOT be null or empty.
      //# The AWS KMS
      //# key identifier MUST be a valid identifier (aws-kms-key-arn.md#a-
      //# valid-aws-kms-identifier).
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      ensures Valid()
      ensures fresh(Repr - {this})
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
      Repr := {this};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
    }

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
    //= type=implication
    //# OnEncrypt MUST take encryption materials (structures.md#encryption-
    //# materials) as input.
    method OnEncrypt(materials: Materials.ValidEncryptionMaterials)
      returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
      //= type=implication
      //# If the input encryption materials (structures.md#encryption-
      //# materials) do not contain a plaintext data key OnEncrypt MUST attempt
      //# to generate a new plaintext data key by calling AWS KMS
      //# GenerateDataKey (https://docs.aws.amazon.com/kms/latest/APIReference/
      //# API_GenerateDataKey.html).
      ensures
        && materials.plaintextDataKey.None?
      ==>
        GenerateDataKeyCalledWith(
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
          //= type=implication
          //# If the keyring calls AWS KMS GenerateDataKeys, it MUST use the
          //# configured AWS KMS client to make the call.
          client,
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
          //= type=implication
          //# The keyring MUST call
          //# AWS KMS GenerateDataKeys with a request constructed as follows:
          GenerateDataKeyRequest(
            materials.encryptionContext,
            grantTokens,
            awsKmsKey,
            materials.algorithmSuiteID.KDFInputKeyLength() as int32
          ))

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
      //= type=implication
      //# *  OnEncrypt MUST output the modified encryption materials
      //# (structures.md#encryption-materials)
      ensures 
        && materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.plaintextDataKey.Some?
        && |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //= type=implication
        //# If the Generate Data Key call succeeds, OnEncrypt MUST verify that
        //# the response "Plaintext" length matches the specification of the
        //# algorithm suite (algorithm-suites.md)'s Key Derivation Input Length
        //# field.
        && materials.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.value)
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //= type=implication
        //# If verified, OnEncrypt MUST do the following with the response
        //# from AWS KMS GenerateDataKey
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html):
        && GenerateDataKeyResult(
            Last(res.value.encryptedDataKeys).ciphertext,
            res.value.plaintextDataKey.value
          )

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
      //= type=implication
      //# Given a plaintext data key in the encryption materials
      //# (structures.md#encryption-materials), OnEncrypt MUST attempt to
      //# encrypt the plaintext data key using the configured AWS KMS key
      //# identifier.
      ensures 
        && materials.plaintextDataKey.Some?
      ==>
        && EncryptCalledWith(
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
          //= type=implication
          //# The keyring MUST call AWS KMS Encrypt
          //# (https://docs.aws.amazon.com/kms/latest/APIReference/
          //# API_Encrypt.html) using the configured AWS KMS client.
          client,
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
          //= type=implication
          //# The keyring
          //# MUST AWS KMS Encrypt call with a request constructed as follows:
          EncryptRequest(
            materials.encryptionContext,
            grantTokens,
            awsKmsKey,
            materials.plaintextDataKey.value
          ))

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
      //= type=implication
      //# If all Encrypt calls succeed, OnEncrypt MUST output the modified
      //# encryption materials (structures.md#encryption-materials).
      ensures 
        && materials.plaintextDataKey.Some?
        && res.Success?
      ==>
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //= type=implication
        //# If verified, OnEncrypt MUST do the following with the
        //# response from AWS KMS Encrypt
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html):
        && |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1
        && EncryptResult(Last(res.value.encryptedDataKeys).ciphertext)
    {
      if materials.plaintextDataKey.None? {
        var generatorRequest := GenerateDataKeyRequest(
          materials.encryptionContext,
          grantTokens,
          awsKmsKey,
          materials.algorithmSuiteID.KDFInputKeyLength() as int32
        );

        var maybeGenerateResponse := GenerateDataKey(client, generatorRequest);

        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //# If the call to AWS KMS GenerateDataKey
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_GenerateDataKey.html) does not succeed, OnEncrypt MUST NOT modify
        //# the encryption materials (structures.md#encryption-materials) and
        //# MUST fail.
        if maybeGenerateResponse.Failure? {
          return Failure(maybeGenerateResponse.error);
        }
        var generateResponse := maybeGenerateResponse.value;

        :- Need(generateResponse.IsWellFormed(), "Invalid response from KMS GenerateDataKey");
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //# The Generate Data Key response's "KeyId" MUST be A valid AWS
        //# KMS key ARN (aws-kms-key-arn.md#identifying-an-aws-kms-multi-region-
        //# key).
        :- Need(
          ParseAwsKmsIdentifier(generateResponse.keyID).Success?,
          "Invalid response from KMS GenerateDataKey:: Invalid Key Id"
        );
        :- Need(
          materials.algorithmSuiteID.ValidPlaintextDataKey(generateResponse.plaintext),
          "Invalid response from AWS KMS GenerateDataKey: Invalid data key"
        );

        var providerInfo :- UTF8.Encode(generateResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, "AWS KMS Key ID too long.");

        var edk := Materials.EncryptedDataKey(
          PROVIDER_ID,
          providerInfo,
          generateResponse.ciphertextBlob
        );
        var plaintextDataKey := generateResponse.plaintext;

        var result := materials.WithKeys(Some(plaintextDataKey), [edk]);
        return Success(result);
      } else {
        var encryptRequest := KMSUtils.EncryptRequest(
          materials.encryptionContext,
          grantTokens,
          awsKmsKey,
          materials.plaintextDataKey.value
        );
        var maybeEncryptResponse := KMSUtils.Encrypt(client, encryptRequest);

        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //= type=implication
        //# If the call to AWS KMS Encrypt
        //# (https://docs.aws.amazon.com/kms/latest/APIReference/
        //# API_Encrypt.html) does not succeed, OnEncrypt MUST fail.
        if maybeEncryptResponse.Failure? {
          return Failure(maybeEncryptResponse.error);
        }

        var encryptResponse := maybeEncryptResponse.value;
        :- Need(encryptResponse.IsWellFormed(), "Invalid response from KMS Encrypt");
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.7
        //# If the Encrypt call succeeds The response's "KeyId" MUST be A valid
        //# AWS KMS key ARN (aws-kms-key-arn.md#identifying-an-aws-kms-multi-
        //# region-key).
        :- Need(
          ParseAwsKmsIdentifier(encryptResponse.keyID).Success?,
          "Invalid response from AWS KMS Encrypt:: Invalid Key Id"
        );

        var providerInfo :- UTF8.Encode(encryptResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, "AWS KMS Key ID too long.");

        var edk := Materials.EncryptedDataKey(
          PROVIDER_ID,
          providerInfo,
          encryptResponse.ciphertextBlob
        );

        var result := materials.WithKeys(materials.plaintextDataKey, [edk]);
        return Success(result);
      }
    }

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
    //= type=implication
    //# OnDecrypt MUST take decryption materials (structures.md#decryption-
    //# materials) and a list of encrypted data keys
    //# (structures.md#encrypted-data-key) as input.
    method OnDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKeys: seq<Materials.EncryptedDataKey>
    )
      returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
      //= type=implication
      //# If the decryption materials (structures.md#decryption-materials)
      //# already contained a valid plaintext data key OnDecrypt MUST
      //# immediately return the unmodified decryption materials
      //# (structures.md#decryption-materials).
      ensures
        materials.plaintextDataKey.Some?
      ==>
        && res.Success?
        && res.value == materials

      ensures
        && materials.plaintextDataKey.None?
        && res.Success?
      ==>
        && res.value.plaintextDataKey.Some?
        && exists edk | edk in encryptedDataKeys
        ::
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
          //= type=implication
          //# *  Its provider ID MUST exactly match the value "aws-kms".
          && edk.providerID == PROVIDER_ID
          && DecryptCalledWith(
            //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
            //= type=implication
            //# To attempt to decrypt a particular encrypted data key
            //# (structures.md#encrypted-data-key), OnDecrypt MUST call AWS KMS
            //# Decrypt (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html) with the configured AWS KMS client.
            client,
            //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
            //= type=implication
            //# When calling AWS KMS Decrypt
            //# (https://docs.aws.amazon.com/kms/latest/APIReference/
            //# API_Decrypt.html), the keyring MUST call with a request constructed
            //# as follows:
            DecryptRequest(
              awsKmsKey,
              edk.ciphertext,
              materials.encryptionContext,
              grantTokens
            ))
          && DecryptResult(
            //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
            //= type=implication
            //# *  The "KeyId" field in the response MUST equal the configured AWS
            //# KMS key identifier.
            awsKmsKey,
            //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
            //= type=implication
            //# If the response does satisfies these requirements then OnDecrypt MUST
            //# do the following with the response:
            res.value.plaintextDataKey.value)
          //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
          //= type=implication
          //# *  The length of the response's "Plaintext" MUST equal the key
          //# derivation input length (algorithm-suites.md#key-derivation-input-
          //# length) specified by the algorithm suite (algorithm-suites.md)
          //# included in the input decryption materials
          //# (structures.md#decryption-materials).
          && materials.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.value)

    {

      if (materials.plaintextDataKey.Some?) {
        return Success(materials);
      }

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
      //# The set of encrypted data keys MUST first be filtered to match this
      //# keyring's configuration.
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsArn);
      var edksToAttempt :- FilterWithResult(filter, encryptedDataKeys);

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
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

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
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
            && edk in encryptedDataKeys
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
          Success(mat)
        //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
        //# If OnDecrypt fails to successfully decrypt any encrypted data key
        //# (structures.md#encrypted-data-key), then it MUST yield an error that
        //# includes all the collected errors.
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
    extends ActionWithResult<Materials.EncryptedDataKey, bool, string>
  {
    const awsKmsKey: AwsKmsIdentifier

    constructor(awsKmsKey: AwsKmsIdentifier) {
      this.awsKmsKey := awsKmsKey;
    }

    predicate Ensures(
      edk: Materials.EncryptedDataKey,
      res: Result<bool, string>
    ) {
      && (
          && res.Success?
          && res.value
        ==>
          edk.providerID == PROVIDER_ID)
    }

    method Invoke(edk: Materials.EncryptedDataKey)
      returns (res: Result<bool, string>)
      ensures Ensures(edk, res)
    {

      if edk.providerID != PROVIDER_ID {
        return Success(false);
      }

      if !UTF8.ValidUTF8Seq(edk.providerInfo) {
        // The Keyring produces UTF8 providerInfo.
        // If an `aws-kms` encrypted data key's providerInfo is not UTF8
        // this is an error, not simply an EDK to filter out.
        return Failure("Invalid AWS KMS encoding, provider info is not UTF8.");
      }

      var keyId :- UTF8.Decode(edk.providerInfo);
      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
      //# *  The provider info MUST be a valid AWS KMS ARN (aws-kms-key-
      //# arn.md#a-valid-aws-kms-arn) with a resource type of "key" or
      //# OnDecrypt MUST fail.
      var arn :- ParseAwsKmsArn(keyId);

      //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.8
      //# *  The the function AWS KMS MRK Match for Decrypt (aws-kms-mrk-match-
      //# for-decrypt.md#implementation) called with the configured AWS KMS
      //# key identifier and the provider info MUST return "true".
      return Success(AwsKmsMrkMatchForDecrypt(
        awsKmsKey,
        AwsKmsArnIdentifier(arn)
      ));
    }
  }

  class DecryptSingleEncryptedDataKey
    extends ActionWithResult<
      Materials.EncryptedDataKey,
      Materials.CompleteDecryptionMaterials,
      string>
  {
    const materials: Materials.PendingDecryptionMaterials
    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMSUtils.GrantTokens

    constructor(
      materials: Materials.PendingDecryptionMaterials,
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
      edk: Materials.EncryptedDataKey,
      res: Result<Materials.CompleteDecryptionMaterials, string>
    ) {
        res.Success?
      ==>
        && res.value.Valid()
        && OnDecryptPure(materials, res)
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
      edk: Materials.EncryptedDataKey
    ) returns (res: Result<Materials.CompleteDecryptionMaterials, string>)
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
        && materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext)
        , "Invalid response from KMS Decrypt");

      var result := materials.WithPlaintextDataKey(decryptResponse.plaintext);
      return Success(result);
    }
  }
}
