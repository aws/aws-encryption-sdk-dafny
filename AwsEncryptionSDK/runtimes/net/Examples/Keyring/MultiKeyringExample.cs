// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrate an encrypt/decrypt cycle using a Multi keyring consisting of an
/// AWS KMS Keyring and a raw AES keyring.
public class MultiKeyringExample
{
    private static void Run(MemoryStream plaintext, string keyArn)
    {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        var encryptionContext = new Dictionary<string, string>()
        {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // Create a KMS keyring to use as the generator.
        var createKeyringInput = new CreateAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn
        };
        var kmsKeyring = materialProviders.CreateAwsKmsKeyring(createKeyringInput);

        // Create a raw AES keyring to additionally encrypt under
        var rawAESKeyring = GetRawAESKeyring(materialProviders);

        // Create a MultiKeyring that consists of the previously created Keyrings.
        // When using this MultiKeyring to encrypt data, either `kmsKeyring` or
        // `rawAESKeyring` (or a MultiKeyring containing either) may be used to decrypt the data.
        var createMultiKeyringInput = new CreateMultiKeyringInput
        {
            Generator = kmsKeyring,
            ChildKeyrings = new List<IKeyring>() {rawAESKeyring}
        };
        var multiKeyring = materialProviders.CreateMultiKeyring(createMultiKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = multiKeyring,
            EncryptionContext = encryptionContext
        };
        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Decrypt your encrypted data using the MultiKeyring used on encrypt.
        // The MultiKeyring will use `kmsKeyring` to decrypt the ciphertext
        // since it is the first available internal keyring which is capable
        // of decrypting the ciphertext.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var multiKeyringDecryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = multiKeyring
        };
        var multiKeyringDecryptOutput = encryptionSdk.Decrypt(multiKeyringDecryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var expectedPair in encryptionContext)
        {
            if (!multiKeyringDecryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var multiKeyringDecrypted = multiKeyringDecryptOutput.Plaintext;
        Assert.Equal(multiKeyringDecrypted.ToArray(), plaintext.ToArray());

        // Demonstrate that you can also successfully decrypt data using the `rawAESKeyring` directly.
        // Because you used a MultiKeyring on Encrypt, you can use either the `kmsKeyring` or
        // `rawAESKeyring` individually to decrypt the data.
        var rawAESKeyringDecryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = rawAESKeyring
        };
        var rawAESKeyringDecryptOutput = encryptionSdk.Decrypt(rawAESKeyringDecryptInput);

        // Verify your Encryption Context
        foreach (var expectedPair in encryptionContext)
        {
            if (!rawAESKeyringDecryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var rawAESKeyringDecrypted = rawAESKeyringDecryptOutput.Plaintext;
        Assert.Equal(rawAESKeyringDecrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestMultiKeyringExample()
    {
        Run(
            GetPlaintextStream(),
            GetDefaultRegionKmsKeyArn()
        );
    }
}
