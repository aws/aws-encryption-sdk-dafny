// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Defs.dfy"
include "../../Materials.dfy"
include "../../AlgorithmSuite.dfy"
include "../../../StandardLibrary/StandardLibrary.dfy"
include "../../../KMS/KMSUtils.dfy"
include "../../../KMS/AmazonKeyManagementService.dfy"
include "../../../KMS/AwsKmsArnParsing.dfy"
include "../../../Util/UTF8.dfy"
include "../../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../../libraries/src/Collections/Sequences/Closures.dfy"
include "../../Serializable.dfy"
include "Constants.dfy"

module {:extern "AwsKmsMrkAwareSymmetricKeyring"} AwsKmsMrkAwareSymmetricKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Seq
  import opened Closures
  import opened Constants
  import Serializable
  import AlgorithmSuite
  import opened KeyringDefs
  import Materials
  import KMSUtils
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
    const awsKmsKeyUtf8Bytes: Serializable.UINT16Seq
    const grantTokens: KMSUtils.GrantTokens

    constructor (
      client: IAmazonKeyManagementService,
      awsKmsKey: string,
      grantTokens: seq<KMSUtils.GrantToken>
    )
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      requires 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
    {
      var awsKmsKeyUtf8Bytes  := UTF8.Encode(awsKmsKey);

      assert ParseAwsKmsIdentifier(awsKmsKey).Success?;

      this.client              := client;
      this.awsKmsKey           := awsKmsKey;
      this.awsKmsKeyUtf8Bytes  := awsKmsKeyUtf8Bytes.value;
      this.grantTokens         := grantTokens;
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials)
      returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
    {

      if materials.plaintextDataKey.None? {
        var generatorRequest := KMSUtils.GenerateDataKeyRequest(
          materials.encryptionContext,
          grantTokens,
          this.awsKmsKey,
          materials.algorithmSuiteID.KDFInputKeyLength() as int32
        );

        var generatorResponse :- KMSUtils.GenerateDataKey(this.client, generatorRequest);

        :- Need(generatorResponse.IsWellFormed(), "Invalid response from KMS GenerateDataKey");
        :- Need(generatorResponse.keyID == this.awsKmsKey, "");
        :- Need(
          materials.algorithmSuiteID.ValidPlaintextDataKey(generatorResponse.plaintext),
          "Invalid response from KMS GenerateDataKey: Invalid key"
        );

        var edk := Materials.EncryptedDataKey(
          PROVIDER_ID,
          this.awsKmsKeyUtf8Bytes,
          generatorResponse.ciphertextBlob
        );
        var plaintextDataKey := generatorResponse.plaintext;

        var result := materials.WithKeys(Some(plaintextDataKey), [edk]);
        return Success(result);
      } else {
        var encryptRequest := KMSUtils.EncryptRequest(
          materials.encryptionContext,
          grantTokens,
          this.awsKmsKey,
          materials.plaintextDataKey.value
        );
        var encryptResponse :- KMSUtils.Encrypt(this.client, encryptRequest);

        :- Need(encryptResponse.IsWellFormed(), "Invalid response from KMS Encrypt");
        :- Need(encryptResponse.keyID == this.awsKmsKey, "Invalid keyId in response from KMS Encrypt");

        var edk := Materials.EncryptedDataKey(
          PROVIDER_ID,
          this.awsKmsKeyUtf8Bytes,
          encryptResponse.ciphertextBlob
        );

        var result := materials.WithKeys(materials.plaintextDataKey, [edk]);
        return Success(result);
      }
    }

    method OnDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKeys: seq<Materials.EncryptedDataKey>
    )
      returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
    {

      if (materials.plaintextDataKey.Some?) {
        return Success(materials);
      }

      var edksToAttempt := Seq.Filter(IsWrappedWithKey, encryptedDataKeys);

      var decryptClosure := new DecryptEncryptedDataKey(
        materials,
        this.client,
        this.awsKmsKey,
        this.grantTokens
      );
      var outcome := Closures.ReduceToSuccess(
        edksToAttempt,
        decryptClosure
      );

      return match outcome {
        case Success(mat) =>
          // This is a bit of a lie, because this is _not_ the EDK that succeded
          assert decryptClosure.Ensures(edksToAttempt[0], Success(mat));
          Success(mat)
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

    predicate method IsWrappedWithKey(edk: Materials.EncryptedDataKey)
    {
      && edk.providerID == PROVIDER_ID
      && edk.providerInfo == this.awsKmsKeyUtf8Bytes
    }

  }

  class DecryptEncryptedDataKey
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
      ensures this.materials == materials
    {
      this.materials := materials;
      this.client := client;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
    }

    predicate Ensures(
      edk: Materials.EncryptedDataKey,
      r: Result<Materials.CompleteDecryptionMaterials, string>
    ) {
      r.Success?
      ==>
        && this.materials.encryptionContext == r.value.encryptionContext
        && this.materials.algorithmSuiteID == r.value.algorithmSuiteID
        && this.materials.verificationKey == r.value.verificationKey
        && r.value.plaintextDataKey.Some?
    }

    method Invoke(
      edk: Materials.EncryptedDataKey
    ) returns (res: Result<Materials.CompleteDecryptionMaterials, string>)
      ensures res.Success? ==> res.value.Valid()
      ensures OnDecryptPure(this.materials, res)
      ensures Ensures(edk, res)
    {

      var decryptRequest := KMSUtils.DecryptRequest(
        this.awsKmsKey,
        edk.ciphertext,
        materials.encryptionContext,
        grantTokens
      );

      var decryptResponse :- KMSUtils.Decrypt(this.client, decryptRequest);

      :- Need(
        && decryptResponse.keyID == this.awsKmsKey
        && this.materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext)
        , "Invalid response from KMS Decrypt");

      var result := this.materials.WithPlaintextDataKey(decryptResponse.plaintext);
      return Success(result);
    }
  }

}
