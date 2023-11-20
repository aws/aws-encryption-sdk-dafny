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
using static ExampleUtils.WriteExampleResources;

/// Demonstrate using Discovery Filters.
///
/// Discovery Filters are used to restrict Discovery Keyrings
/// to trusted AWS Accounts.
/// The Accounts are specified by their Account Ids
/// and the partition they are in.
///
/// It's always a best practice to specify your wrapping keys explicitly.
/// This practice assures that you only use the keys that you intend.
/// It also improves performance by preventing you from
/// inadvertently using keys in a different AWS account or Region,
/// or attempting to decrypt with keys that you don't have permission to use.
///
/// However, when decrypting with AWS KMS keyrings,
/// you are not required to specify wrapping keys.
/// The AWS Encryption SDK can get the key identifier
/// from the metadata of the encrypted data key.
///
/// When specifying AWS KMS wrapping keys for decrypting is impractical
/// (such as when encrypting using AWS KMS Aliases),
/// you can use discovery keyrings.
///
/// When you can not specify your wrapping keys explicitly,
/// using a Discovery Filter is a best practice.
///
/// Particularly if an application is decrypting messages from multiple sources,
/// adding trusted AWS accounts to the discovery filter allows it to
/// protect itself from decrypting messages from untrusted sources.
public class DiscoveryFilterExample
{
    const string fileName = "defaultRegionKmsKey.bin";

    /// <param name="plaintext">unencrypted data</param>
    /// <param name="trustedAccountIds">List of AWS Account Ids that are trusted.</param>
    /// <param name="awsPartition">AWS Partition that contains all the members of "trustedAccountIds".</param>
    /// <exception cref="Exception"></exception>
    private static void Run(
        MemoryStream plaintext,
        List<string> trustedAccountIds,
        string awsPartition
    )
    {
        /* 1. Instantiate the Material Providers and Encryption SDK */
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        // Instantiate the Encryption SDK such that it limits the number of
        // Encrypted Data Keys a ciphertext may contain.
        // Discovery Keyrings are an excellent tool
        // for handling encrypted messages from multiple sources.
        // Limiting the number of encrypted data keys is a best practice,
        // particularly when decrypting messages from multiple sources.
        // See the LimitEncryptedDataKeysExample for details.
        var esdkConfig = new AwsEncryptionSdkConfig
        {
            MaxEncryptedDataKeys = 1
        };
        var encryptionSdk = new ESDK(esdkConfig);

        /* 2. Create a Discovery Keyring with a Discovery Filter */
        // We create a Discovery keyring to use for decryption.
        // We'll add a discovery filter so that we limit the set of Encrypted Data Keys
        // we are willing to decrypt to only ones created by KMS keys from
        // trusted accounts.
        var decryptKeyringInput = new CreateAwsKmsDiscoveryKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            DiscoveryFilter = new DiscoveryFilter
            {
                AccountIds = trustedAccountIds,
                Partition = awsPartition
            }
        };
        var decryptKeyring = materialProviders.CreateAwsKmsDiscoveryKeyring(decryptKeyringInput);

        /* 3. Retrieve or create an encrypted message to decrypt. */
        // To focus on Discovery Filters,
        // we rely on a helper method to load the encrypted message.
        var ciphertext = ReadMessage(fileName);
        Dictionary<string, string> encryptionContext = GetEncryptionContext();

        /* 4. Decrypt the encrypted data. */
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = decryptKeyring
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        /* 5. Verify the encryption context */
        VerifyEncryptionContext(decryptOutput, encryptionContext);

        /* 6. Verify the decrypted plaintext is the original plaintext */
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);

        /* 7. Create a discovery filter that excludes the encrypted data key */
        // If we create a Discovery Filter that excludes
        // all the accounts the ciphertext was encrypted with,
        // the decryption will fail.
        decryptKeyringInput.DiscoveryFilter = new DiscoveryFilter
        {
            AccountIds = new List<string> {"123456789012"},
            Partition = awsPartition
        };

        /* 8. Validate the excluding discovery filter fails to decrypt the ciphertext */
        var decryptFailed = false;
        var failingKeyring = materialProviders.CreateAwsKmsDiscoveryKeyring(decryptKeyringInput);
        decryptInput.Keyring = failingKeyring;
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (AwsCryptographicMaterialProvidersException)
        {
            decryptFailed = true;
        }
        Assert.True(decryptFailed);
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestDiscoveryFilterExample()
    {

        if (!File.Exists(GetResourcePath(fileName)))
        {
            EncryptAndWrite(GetPlaintextStream(), GetDefaultRegionKmsKeyArn(), fileName);
        }
        Run(GetPlaintextStream(), GetAccountIds(), "aws");
    }
}
