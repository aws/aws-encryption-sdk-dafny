// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using Aws.Crypto;
using Aws.Esdk;

using Xunit;

/// Demonstrate an encrypt/decrypt cycle using a Multi-Keyring made up of multiple AWS KMS
/// Keyrings.
public class AwsKmsMultiKeyring {
    private static void Run(MemoryStream plaintext, string keyArn1, string keyArn2, List<string> accountIds, List<string> regions) {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        var encryptionContext = new Dictionary<string, string>() {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Create clients to access the Material Providers and Encryption SDK APIs.
        var materialProvidersClient = AwsCryptographicMaterialProvidersClientFactory.CreateDefaultAwsCryptographicMaterialProvidersClient();
        var encryptionSdkClient = AwsEncryptionSdkClientFactory.CreateDefaultAwsEncryptionSdkClient();

        // Create a AwsKmsMultiKeyring that protects your data under two different KMS Keys.
        // Either KMS Key individually is capable of decrypting data encrypted under this KeyAwsKmsMultiKeyringring.
        var createAwsKmsMultiKeyringInput = new CreateAwsKmsMultiKeyringInput
        {
            Generator = keyArn1,
            KmsKeyIds = new List<string>() { keyArn2 }
        };
        var kmsMultiKeyring = materialProvidersClient.CreateAwsKmsMultiKeyring(createAwsKmsMultiKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = kmsMultiKeyring,
            EncryptionContext = encryptionContext
        };

        var encryptOutput = encryptionSdkClient.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Decrypt your encrypted data using the AwsKmsMultiKeyring.
        // It will decrypt the data using the generator KMS key since
        // it is the first available KMS key on the AwsKmsMultiKeyring that
        // is capable of decrypting the data.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = kmsMultiKeyring
        };
        var decryptOutput = encryptionSdkClient.Decrypt(decryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var (expectedKey, expectedValue) in encryptionContext)
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedKey, out var decryptedValue)
                || !decryptedValue.Equals(expectedValue))
                throw new Exception("Encryption context does not match expected values");

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());

        // Demonstrate that a single AwsKmsKeyring configured with either KMS key
        // is also capable of decrypting the data.
        //
        // Create a single AwsKmsKeyring with one of the KMS keys configured on the AwsKmsMultiKeyring.
        // Create a KMS keyring to use as the generator.
        var createKeyringInput = new CreateAwsKmsKeyringInput
        {
            KmsKeyId = keyArn2
        };
        var kmsKeyring = materialProvidersClient.CreateAwsKmsKeyring(createKeyringInput);

        // Decrypt your encrypted data using the AwsKmsKeyring configured with the single KMS key.
        var kmsKeyringDecryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = kmsKeyring
        };
        var kmsKeyringDecryptOutput = encryptionSdkClient.Decrypt(kmsKeyringDecryptInput);

        // Verify the Encryption Context on the output
        foreach (var (expectedKey, expectedValue) in encryptionContext)
            if (!kmsKeyringDecryptOutput.EncryptionContext.TryGetValue(expectedKey, out var decryptedValue)
                || !decryptedValue.Equals(expectedValue))
                throw new Exception("Encryption context does not match expected values");

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var kmsKeyringDecrypted = kmsKeyringDecryptOutput.Plaintext;
        Assert.Equal(kmsKeyringDecrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMultiKeyringExample()
    {
        Run(
            ExampleUtils.ExampleUtils.GetPlaintextStream(),
            ExampleUtils.ExampleUtils.GetKmsKeyArn(),
            ExampleUtils.ExampleUtils.GetKmsKeyArn2(),
            ExampleUtils.ExampleUtils.GetAccountIds(),
            ExampleUtils.ExampleUtils.GetRegions()
        );
    }
}
