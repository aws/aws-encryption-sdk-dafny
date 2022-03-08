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

/// Demonstrate an encrypt/decrypt cycle using a Multi-Keyring made up of multiple AWS KMS
/// Strict Keyrings.
public class AwsKmsStrictMultiKeyring {
    static void Run(MemoryStream plaintext, string keyArn, List<string> accountIds, List<string> regions) {
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
        AwsCryptographicMaterialProvidersClientConfig providersConfig = new AwsCryptographicMaterialProvidersClientConfig
        {
            ConfigDefaults = Aws.Crypto.ConfigurationDefaults.V1
        };
        IAwsCryptographicMaterialProvidersClient materialProviders = AwsCryptographicMaterialProvidersClientFactory.MakeAwsCryptographicMaterialProvidersClient(providersConfig);

        AwsEncryptionSdkClientConfig clientConfig = new AwsEncryptionSdkClientConfig
        {
            ConfigDefaults = Aws.Esdk.ConfigurationDefaults.V1
        };
        IAwsEncryptionSdkClient encryptionSdkClient = AwsEncryptionSdkClientFactory.MakeAwsEncryptionSdkClient(clientConfig);

        // Create the keyring that determines how your data keys are protected.
        CreateStrictAwsKmsKeyringInput createKeyringInput = new CreateStrictAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn,
        };
        IKeyring keyring = materialProviders.CreateStrictAwsKmsKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        // In this example, we pass a keyring. Behind the scenes, the AWS Encryption SDK will create
        // a default CryptographicMaterialsManager which uses this keyring
        EncryptInput encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = keyring,
            EncryptionContext = encryptionContext
        };

        EncryptOutput encryptOutput = encryptionSdkClient.Encrypt(encryptInput);
        MemoryStream ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());


        // Decrypt your encrypted data using the same keyring you used on encrypt.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        DecryptInput decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = keyring,
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
    public void TestAwsKmsStrictMultiKeyringExample()
    {
        Run(
            ExampleUtils.ExampleUtils.GetPlaintextStream(),
            ExampleUtils.ExampleUtils.GetKmsKeyArn(),
            ExampleUtils.ExampleUtils.GetAccountIds(),
            ExampleUtils.ExampleUtils.GetRegions()
        );
    }
}
