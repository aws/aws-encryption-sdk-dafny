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

module {:extern "AwsKmsMrkAwareSymmetricKeyring"} AwsKmsMrkAwareSymmetricKeyring {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import opened AwsKmsArnParsing
  import opened AmazonKeyManagementService
  import opened Seq
  import AlgorithmSuite
  import KeyringDefs
  import Materials
  import KMSUtils
  import UTF8

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s

    //= compliance/framework/aws-kms/aws-kms-mrk-aware-symmetric-keyring.txt#2.5
    //= type=implication
    //# MUST implement the AWS Encryption SDK Keyring interface (../keyring-
    //# interface.md#interface)
  class AwsKmsMrkAwareSymmetricKeyring 
    extends KeyringDefs.Keyring,
    KeyringDefs.UnwrapSingleEncryptedDataKey
  {

    const client: IAmazonKeyManagementService
    const awsKmsKey: string
    const awsKmsKeyUtf8Bytes: UTF8.ValidUTF8Bytes
    const awsKmsKeyIdentifier: AwsKmsIdentifier
    const grantTokens: seq<KMSUtils.GrantToken>

    constructor (
      client: IAmazonKeyManagementService,
      awsKmsKey: string,
      grantTokens: seq<KMSUtils.GrantToken>
    )
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?;
    {
      var awsKmsKeyIdentifier := ParseAwsKmsIdentifier(awsKmsKey);
      var awsKmsKeyUtf8Bytes  := UTF8.Encode(awsKmsKey);

      this.client              := client;
      this.awsKmsKey           := awsKmsKey;
      this.awsKmsKeyIdentifier := awsKmsKeyIdentifier.value;
      this.awsKmsKeyUtf8Bytes  := awsKmsKeyUtf8Bytes.value;
      this.grantTokens         := grantTokens;
    }

    predicate Valid()
      // reads this, Repr
      // ensures Valid() ==> this in Repr
    {
      true
      // && this in Repr
      // && 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      // && (|keyIDs| == 0 && generator.None? ==> isDiscovery)
      // && (clientSupplier in Repr && clientSupplier.Repr <= Repr && this !in clientSupplier.Repr && clientSupplier.Valid())
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
    {
      var resultMaterials: Materials.ValidEncryptionMaterials;

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

        var encryptedDataKey := Materials.EncryptedDataKey(
          PROVIDER_ID,
          this.awsKmsKeyUtf8Bytes, 
          generatorResponse.ciphertextBlob
        );
        var plaintextDataKey := generatorResponse.plaintext;

        var newEncryptedDataKeys := [encryptedDataKey];
        var result := materials.WithKeys(Some(plaintextDataKey), newEncryptedDataKeys);
        return Success(result);
      } else {
        var encryptRequest := KMSUtils.EncryptRequest(
          materials.encryptionContext,
          grantTokens,
          this.awsKmsKey,
          resultMaterials.plaintextDataKey.value
        );
        var encryptResponse :- KMSUtils.Encrypt(this.client, encryptRequest);

        :- Need(encryptResponse.IsWellFormed(), "Invalid response from KMS Encrypt");
        :- Need(encryptResponse.keyID == this.awsKmsKey, "Invalid keyId in response from KMS Encrypt");

        var edk := Materials.EncryptedDataKey(
          PROVIDER_ID,
          this.awsKmsKeyUtf8Bytes,
          encryptResponse.ciphertextBlob
        );
        resultMaterials := resultMaterials.WithKeys(resultMaterials.plaintextDataKey, [edk]);

        return Success(resultMaterials);
      }
    }

    method OnDecrypt(
      materials: Materials.ValidDecryptionMaterials,
      edks: seq<Materials.EncryptedDataKey>
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
    {

      if (materials.plaintextDataKey.Some?) {
        return Success(materials);
      }

      var edksToAttempt := Seq.Filter(ShouldAttemptDecryption, edks);

      var outcome := this.FirstSuccessufulDecrypt(
        materials,
        edksToAttempt,
        "Unable to decrypt data key: No EDKs supplied",
        "Unable to decrypt data key: "
      );

      return outcome;
    }

    method Decrypt(
      materials: Materials.ValidDecryptionMaterials,
      encryptedDataKey: Materials.EncryptedDataKey
    ) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
    {
      var decryptRequest := KMSUtils.DecryptRequest(
        this.awsKmsKey,
        encryptedDataKey.ciphertext,
        materials.encryptionContext,
        grantTokens
      );

      var decryptResponse :- KMSUtils.Decrypt(this.client, decryptRequest);

      :- Need(
        && decryptResponse.keyID == this.awsKmsKey
        && materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext)
        , "Invalid response from KMS Decrypt");

      var result := materials.WithPlaintextDataKey(decryptResponse.plaintext);
      return Success(result);
    }

    predicate method ShouldAttemptDecryption(edk: Materials.EncryptedDataKey)
    {
      && edk.providerID == PROVIDER_ID
      && edk.providerInfo == this.awsKmsKeyUtf8Bytes
    }

  }

}
