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

/// Demonstrate an encrypt/decrypt cycle using a Multi-Keyring containing multiple AWS KMS
/// MRK Discovery Keyrings.
public class AwsKmsMrkDiscoveryMultiKeyringExample
{
    private static void Run(MemoryStream plaintext, string keyArn, List<string> accountIds, List<string> regions)
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
        // a KMS keyring without discovery.
        var createKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient( // Create a KMS Client for the region of the Encrypt MRK Key
                RegionEndpoint.GetBySystemName(GetRegionStringFromArn(keyArn))),
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
            DiscoveryFilter = new DiscoveryFilter()
            {
                AccountIds = accountIds,
                Partition = "aws"
            }
        };

        // This is a Multi Keyring composed of MRK Discovery Keyrings.
        // All the keyrings have the same Discovery Filter,
        // (and would have the same Grant Tokens, if passed a Grant Token list).
        // Each Keyring has its own KMS Client.
        // These KMS Clients are provisioned by the DefaultClientSupplier,
        // since no ClientSupplier was given to the input object.
        var multiKeyring = materialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring(createDecryptKeyringInput);

        // On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
        // The header contains the Encrypted Data Keys (EDKs), which include the KMS Key arn.
        // For each member of the Multi Keyring, every EDK will try to be decrypted until a decryption is successful.
        // Since every member of the Multi Keyring is a Discovery Keyring:
        //   Each Keyring will filter the EDKs by the Discovery Filter
        //      For the filtered EDKs, the keyring will try to decrypt it with the keyring's client.
        // All of this is done serially, until a success occurs or all keyrings have failed all (filtered) EDKs.
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
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMrkDiscoveryMultiKeyringExample()
    {
        Run(
            GetPlaintextStream(),
            GetDefaultRegionMrkKeyArn(),
            GetAccountIds(),
            GetRegions()
        );
    }
}
