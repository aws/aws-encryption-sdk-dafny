// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using Aws.Crypto;
using Aws.Esdk;

using Xunit;
using ConfigurationDefaults = Aws.Esdk.ConfigurationDefaults;

/// Demonstrate an encrypt/decrypt cycle using a AWS KMS MRK-aware discovery keyring.
public class AwsKmsMrkAwareDiscoveryKeyringExample {
    static void Run(MemoryStream plaintext, string keyArn) {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        Dictionary<string, string> encryptionContext = new Dictionary<string, string>() {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Create clients to access the Encryption SDK APIs.
        // TODO: add client configuration objects
        IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();
        AwsEncryptionSdkClientConfig config = new AwsEncryptionSdkClientConfig
        {
            ConfigDefaults = ConfigurationDefaults.V1
        };
        IAwsEncryptionSdk encryptionSdkClient = new AwsEncryptionSdkClient(config);

        // Create the keyring that determines how your data keys are protected. Though this example highlights
        // Discovery keyrings, Discovery keyrings cannot be used to encrypt, so we create a Strict KMS keyring
        // for encryption.
        CreateMrkAwareStrictAwsKmsKeyringInput createKeyringInput = new CreateMrkAwareStrictAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn,
        };
        IKeyring encryptKeyring = materialProviders.CreateMrkAwareStrictAwsKmsKeyring(createKeyringInput);

        // Create the materials manager that assembles cryptographic materials from your keyring.
        CreateDefaultCryptographicMaterialsManagerInput createEncryptCmmInput =
            new CreateDefaultCryptographicMaterialsManagerInput {Keyring = encryptKeyring};
        ICryptographicMaterialsManager encryptCmm =
            materialProviders.CreateDefaultCryptographicMaterialsManager(createEncryptCmmInput);

        // Encrypt your plaintext data.
        EncryptInput encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = encryptCmm,
            EncryptionContext = encryptionContext,
        };
        EncryptOutput encryptOutput = encryptionSdkClient.Encrypt(encryptInput);
        MemoryStream ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Now create a Discovery keyring to use for decryption.
        CreateMrkAwareDiscoveryAwsKmsKeyringInput createDecryptKeyringInput = new CreateMrkAwareDiscoveryAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            Region = "us-west-2"
        };
        IKeyring decryptKeyring = materialProviders.CreateMrkAwareDiscoveryAwsKmsKeyring(createDecryptKeyringInput);
        CreateDefaultCryptographicMaterialsManagerInput createDecryptCmmInput =
            new CreateDefaultCryptographicMaterialsManagerInput {Keyring = decryptKeyring};
        ICryptographicMaterialsManager decryptCmm =
            materialProviders.CreateDefaultCryptographicMaterialsManager(createDecryptCmmInput);

        DecryptInput decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            MaterialsManager = decryptCmm,
        };
        DecryptOutput decryptOutput = encryptionSdkClient.Decrypt(decryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var (expectedKey, expectedValue) in encryptionContext)
        {
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedKey, out var decryptedValue)
                || !decryptedValue.Equals(expectedValue))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        MemoryStream decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMrkAwareDiscoveryKeyringExample() {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream(), ExampleUtils.ExampleUtils.GetKmsKeyArn());
    }
}
