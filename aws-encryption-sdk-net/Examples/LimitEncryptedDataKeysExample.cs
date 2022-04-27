// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrate limiting the number of Encrypted Data Keys [EDKs] allowed
/// when encrypting or decrypting a message.
/// Limiting encrypted data keys is most valuable when you are decrypting
/// messages from an untrusted source.
/// By default, the ESDK will allow up to 65,535 encrypted data keys.
/// A malicious actor might construct an encrypted message with thousands of
/// encrypted data keys, none of which can be decrypted.
/// As a result, the AWS Encryption SDK would attempt to decrypt each
/// encrypted data key until it exhausted the encrypted data keys in the message.
public class LimitEncryptedDataKeysExample
{
    private static void Run(MemoryStream plaintext, int maxEncryptedDataKeys)
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

        // Instantiate the Material Providers
        var materialProviders =
            AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
        // Set the EncryptionSDK's MaxEncryptedDataKeys parameter
        var esdkConfig = new AwsEncryptionSdkConfig
        {
            MaxEncryptedDataKeys = maxEncryptedDataKeys
        };
        // Instantiate the EncryptionSDK with the configuration
        var encryptionSdk = AwsEncryptionSdkFactory.CreateAwsEncryptionSdk(esdkConfig);

        // We will use a helper method to create a Multi Keyring with `maxEncryptedDataKeys` AES Keyrings
        var keyrings = new Queue<IKeyring>();
        for (long i = 1; i <= maxEncryptedDataKeys; i++)
        {
            keyrings.Enqueue(GetRawAESKeyring(materialProviders));
        }
        var createMultiKeyringInput = new CreateMultiKeyringInput
        {
            Generator = keyrings.Dequeue(),
            ChildKeyrings = keyrings.ToList()
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

        // Decrypt your encrypted data using the same keyring you used on encrypt.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = multiKeyring
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var expectedPair in encryptionContext)
        {
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());

        // Demonstrate that an EncryptionSDK with a lower MaxEncryptedDataKeys
        // will fail to decrypt the encrypted message.
        var failedDecryption = false;
        esdkConfig = new AwsEncryptionSdkConfig
        {
            MaxEncryptedDataKeys = maxEncryptedDataKeys - 1
        };
        // Instantiate the EncryptionSDK with the configuration
        encryptionSdk = AwsEncryptionSdkFactory.CreateAwsEncryptionSdk(esdkConfig);

        // Repeat the earlier decryption steps, proving that they fail
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
#pragma warning disable 168
        catch (AwsEncryptionSdkException ignore)
#pragma warning restore 168
        {
            failedDecryption = true;
        }
        Assert.True(failedDecryption);
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestLimitEncryptedDataKeysExample()
    {
        Run(GetPlaintextStream(), 3);
    }
}
