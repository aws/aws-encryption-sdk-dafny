// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using Aws.Crypto;
using Aws.Esdk;

using Xunit;
using ConfigurationDefaults = Aws.Esdk.ConfigurationDefaults;

/// Demonstrate an encrypt/decrypt cycle using a AWS MRK-aware symmetric keyring.
public class StrictAwsKmsKeyringExample {
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

        // Create the keyring that determines how your data keys are protected.
        CreateStrictAwsKmsKeyringInput createKeyringInput = new CreateStrictAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn,
        };
        IKeyring keyring = materialProviders.CreateStrictAwsKmsKeyring(createKeyringInput);

        // Create the materials manager that assembles cryptographic materials from your keyring.
        CreateDefaultCryptographicMaterialsManagerInput createMaterialsManagerInput =
            new CreateDefaultCryptographicMaterialsManagerInput {Keyring = keyring};
        ICryptographicMaterialsManager materialsManager =
            materialProviders.CreateDefaultCryptographicMaterialsManager(createMaterialsManagerInput);

        // Encrypt your plaintext data.
        EncryptInput encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = materialsManager,
            EncryptionContext = encryptionContext,
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
            MaterialsManager = materialsManager,
        };
        DecryptOutput decryptOutput = encryptionSdkClient.Decrypt(decryptInput);
        MemoryStream decrypted = decryptOutput.Plaintext;

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());

        // Verify that the encryption context used in the decrypt operation includes
        // the encryption context that you specified when encrypting.
        // The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        // TODO: Add logic that checks the encryption context.
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestStrictAwsKmsKeyringExample() {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream(), ExampleUtils.ExampleUtils.GetKmsKeyArn());
    }
}
