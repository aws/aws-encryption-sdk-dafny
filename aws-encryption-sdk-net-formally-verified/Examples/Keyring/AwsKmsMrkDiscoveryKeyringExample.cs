// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon;
using Amazon.KeyManagementService;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
using Xunit;

/// Demonstrate an encrypt/decrypt cycle using an AWS KMS MRK discovery keyring.
public class AwsKmsMrkDiscoveryKeyringExample
{
    private static void Run(MemoryStream plaintext, string encryptKeyArn, string decryptRegion)
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
        var materialProviders =
            AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
        var encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

        // Create the keyring that determines how your data keys are protected. Though this example highlights
        // Discovery keyrings, Discovery keyrings cannot be used to encrypt, so for encryption we create
        // a KMS keyring without discovery mode.
        var encryptRegion = Arn.Parse(encryptKeyArn).Region;
        var createKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(encryptRegion)),
            KmsKeyId = encryptKeyArn
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

        // Now create a Discovery keyring to use for decryption. In order to illustrate the MRK behavior of this
        // keyring, we configure the keyring to use the second KMS region where the MRK is replicated to.
        var createDecryptKeyringInput = new CreateAwsKmsMrkDiscoveryKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(decryptRegion)),
            Region = decryptRegion,
            DiscoveryFilter = new DiscoveryFilter()
            {
                AccountIds = ExampleUtils.ExampleUtils.GetAccountIds(),
                Partition = "aws"
            }
        };
        var decryptKeyring = materialProviders.CreateAwsKmsMrkDiscoveryKeyring(createDecryptKeyringInput);

        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = decryptKeyring
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
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMrkDiscoveryKeyringExample()
    {
        Run(
            ExampleUtils.ExampleUtils.GetPlaintextStream(),
            ExampleUtils.ExampleUtils.GetDefaultRegionMrkKeyArn(),
            Arn.Parse(ExampleUtils.ExampleUtils.GetAlternateRegionMrkKeyArn()).Region
        );
    }
}
