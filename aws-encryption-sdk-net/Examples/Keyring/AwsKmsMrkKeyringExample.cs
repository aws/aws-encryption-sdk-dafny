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
using static ExampleUtils.ExampleUtils;

/// Demonstrate an encrypt/decrypt cycle using an AWS MRK keyring.
public class AwsKmsMrkKeyringExample
{
    private static void Run(MemoryStream plaintext, string encryptKeyArn, string decryptKeyArn)
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

        // Create a keyring that will encrypt your data, using a KMS MRK key in the first region.
        var createEncryptKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(GetRegionEndpointFromArn(encryptKeyArn)),
            KmsKeyId = encryptKeyArn
        };
        var encryptKeyring = materialProviders.CreateAwsKmsMrkKeyring(createEncryptKeyringInput);

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

        // Create a keyring that will decrypt your data, using the same KMS MRK key replicated to the second region.
        // This example assumes you have already replicated your key; for more info on this, see the KMS documentation:
        // https://docs.aws.amazon.com/kms/latest/developerguide/multi-region-keys-overview.html
        var createDecryptKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(GetRegionEndpointFromArn(decryptKeyArn)),
            KmsKeyId = decryptKeyArn
        };
        var decryptKeyring = materialProviders.CreateAwsKmsMrkKeyring(createDecryptKeyringInput);

        // Decrypt your encrypted data using the decrypt keyring.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
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
    public void TestAwsKmsMrkKeyringExample()
    {
        Run(
            GetPlaintextStream(),
            GetDefaultRegionMrkKeyArn(),
            GetAlternateRegionMrkKeyArn()
        );
    }
}
