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

/// Demonstrate decryption using an AWS KMS MRK discovery keyring.
public class AwsKmsMrkDiscoveryKeyringExample
{
    private static void Run(MemoryStream plaintext, string encryptKeyArn, RegionEndpoint decryptRegion)
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

        // Create the keyring that determines how your data keys are protected.
        // Though this example highlights MRK Discovery keyrings,
        // MRK Discovery keyrings cannot be used to encrypt, so for encryption
        // we create a KMS MRK keyring.
        var createKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(GetRegionEndpointFromArn(encryptKeyArn)),
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

        // Now create a Discovery keyring to use for decryption.
        // In order to illustrate the MRK behavior of this keyring, we configure
        // the keyring to use the second KMS region where the MRK is replicated to.
        var createDecryptKeyringInput = new CreateAwsKmsMrkDiscoveryKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(decryptRegion),
            Region = decryptRegion.SystemName
        };
        var decryptKeyring = materialProviders.CreateAwsKmsMrkDiscoveryKeyring(createDecryptKeyringInput);

        // On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
        // The header contains the Encrypted Data Keys (EDKs), which, if the EDK
        // was encrypted by a KMS Keyring, includes the KMS Key ARN.
        // The MRK Discovery Keyring filters these EDKs for:
        // - EDKs encrypted by Single Region KMS Keys in the keyring's region
        // OR
        // - EDKs encrypted by Multi Region KMS Keys
        // Additionally, the keyring would filter these KMS encrypted data keys
        // by the keyring's Discovery Filter, if a Discovery Filter is
        // present on the keyring.
        // Finally, KMS is called to decrypt each filtered EDK until an EDK is
        // successfully decrypted. The resulting data key is used to decrypt the
        // ciphertext's message.
        // If all calls to KMS fail, the decryption fails.
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
            GetPlaintextStream(),
            GetDefaultRegionMrkKeyArn(),
            GetRegionEndpointFromArn(GetAlternateRegionMrkKeyArn())
        );
    }
}
