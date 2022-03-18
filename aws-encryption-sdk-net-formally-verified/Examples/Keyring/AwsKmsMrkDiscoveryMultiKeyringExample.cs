// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using Aws.EncryptionSdk;
using Aws.EncryptionSdk.Core;

using Xunit;

/// Demonstrate an encrypt/decrypt cycle using a Multi-Keyring containing multiple AWS KMS
/// MRK Discovery Keyrings.
public class AwsKmsMrkDiscoveryMultiKeyringExample {
    private static void Run(MemoryStream plaintext, string keyArn, List<string> accountIds, List<string> regions) {
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

        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
        var encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

        // Create the keyring that determines how your data keys are protected. Though this example highlights
        // Discovery keyrings, Discovery keyrings cannot be used to encrypt, so for encryption we create
        // a KMS keyring without discovery mode.
        var createKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn
        };
        var encryptKeyring = materialProviders.CreateAwsKmsMrkKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = encryptKeyring,
            EncryptionContext = encryptionContext
        };

        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Now create a Discovery keyring to use for decryption. We'll add a discovery filter so that we limit
        // the set of ciphertexts we are willing to decrypt to only ones created by KMS keys in our region and
        // partition.
        var createDecryptKeyringInput = new CreateAwsKmsMrkDiscoveryMultiKeyringInput
        {
            Regions = regions,
            DiscoveryFilter = new DiscoveryFilter() {
                AccountIds = accountIds,
                Partition = "aws"
            }
        };
        var keyring = materialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring(createDecryptKeyringInput);

        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = keyring
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var tuple in encryptionContext)
            if (!decryptOutput.EncryptionContext.TryGetValue(tuple.Key, out var decryptedValue)
                || !decryptedValue.Equals(tuple.Value))
                throw new Exception("Encryption context does not match expected values");

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMrkDiscoveryMultiKeyringExample()
    {
        Run(
            ExampleUtils.ExampleUtils.GetPlaintextStream(),
            ExampleUtils.ExampleUtils.GetDefaultRegionKmsKeyArn(),
            ExampleUtils.ExampleUtils.GetAccountIds(),
            ExampleUtils.ExampleUtils.GetRegions()
        );
    }
}
