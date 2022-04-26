// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using Amazon.KeyManagementService;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrate using Discovery Filters.
/// Discovery Filters are used to restrict Discovery Keyrings
/// to trusted AWS Accounts.
/// The Accounts are specified by their Account Ids
/// and the partition they are in.
/// It's always a best practice to specify your wrapping keys explicitly when
/// decrypting. This practice assures that you only use the keys that you intend.
/// It also improves performance by preventing you from inadvertently using keys
/// in a different AWS account or Region, or attempting to decrypt with keys that
/// you don't have permission to use.
/// However, when decrypting with AWS KMS keyrings, you are not required to specify
/// wrapping keys. The AWS Encryption SDK can get the key identifier from the
/// metadata of the encrypted data key.
/// When specifying AWS KMS wrapping keys for decrypting is impractical (such as when
/// encrypting using AWS KMS Aliases), you can use discovery keyrings.
/// When you can not specify your wrapping keys explicitly,
/// using a Discovery Filter is a best practice.
/// Particularly if an application is decrypting messages from multiple sources,
/// adding trusted AWS accounts to the discovery filter allows it to
/// protect itself from decrypting messages from untrusted sources.
public class DiscoveryFilterExample
{
    /// <param name="plaintext">Data to be encrypted</param>
    /// <param name="encryptKeyArn">KMS Key Arn to encrypt the plaintext under</param>
    /// <param name="trustedAccountIds">List of AWS Account Ids that are trusted.</param>
    /// <param name="awsPartition">AWS Partition that contains all the members of "trustedAccountIds".</param>
    /// <exception cref="Exception"></exception>
    private static void Run(
        MemoryStream plaintext,
        string encryptKeyArn,
        List<string> trustedAccountIds,
        string awsPartition
    )
    {
        // Instantiate the Material Providers
        var materialProviders =
            AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();

        // Instantiate the Encryption SDK such that it limits the number of
        // Encrypted Data Keys a ciphertext may contain.
        // This is a best practice, particularly when decrypting messages from
        // multiple sources.
        // See the <code>LimitEncryptedDataKeysExample</code> for details.
        var esdkConfig = new AwsEncryptionSdkConfig
        {
            MaxEncryptedDataKeys = GetMaxExampleKeys()
        };
        var encryptionSdk = AwsEncryptionSdkFactory.CreateAwsEncryptionSdk(esdkConfig);

        // To focus on Discovery Filters, we will rely on a helper method
        // to create the encrypted message (ciphertext).
        Dictionary<string, string> encryptionContext;
        MemoryStream ciphertext;
        (encryptionContext, ciphertext) = EncryptMessageWithKMSKey(
            plaintext, encryptKeyArn, materialProviders, encryptionSdk);

        // Now create a Discovery keyring to use for decryption.
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

        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = decryptKeyring
        };
        // If the `encryptKeyArn` is from an AWS Account in `trustedAccountIds`,
        // then the Encryption SDK will attempt to decrypt it.
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);
        VerifyEncryptionContext(decryptOutput, encryptionContext);
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);

        // If we create a Discovery Filter that excludes the account the
        // `encryptKeyArn` is from, the decryption will fail.
        var decryptFailed = false;
        decryptKeyringInput.DiscoveryFilter = new DiscoveryFilter
        {
            AccountIds = new List<string> {"123456789012"},
            Partition = awsPartition
        };
        var failingKeyring = materialProviders.CreateAwsKmsDiscoveryKeyring(decryptKeyringInput);
        decryptInput.Keyring = failingKeyring;
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (AwsEncryptionSdkException)
        {
            decryptFailed = true;
        }

        Assert.True(decryptFailed);
    }

    /// <summary>
    ///     To focus on Discovery Filters, we rely on this helper method
    ///     to create the encrypted message (ciphertext) with the given KMS Key.
    /// </summary>
    private static (Dictionary<string, string> encryptionContext, MemoryStream ciphertext) EncryptMessageWithKMSKey(
        MemoryStream plaintext, string kmsKeyArn, IAwsCryptographicMaterialProviders materialProviders,
        IAwsEncryptionSdk encryptionSdk)
    {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        var encryptionContext = new Dictionary<string, string>
        {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Create the keyring that determines how your data keys are protected.
        // Though this example highlights Discovery Filters, Discovery keyrings
        // cannot be used to encrypt, so for encryption we create
        // a KMS keyring without discovery mode.
        var createKeyringInput = new CreateAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = kmsKeyArn
        };
        var encryptKeyring = materialProviders.CreateAwsKmsKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = encryptKeyring,
            EncryptionContext = encryptionContext
        };
        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;
        return (encryptionContext, ciphertext);
    }

    /// <summary>
    ///     For this example, we break out the Encryption Context Verification
    ///     into a helper method.
    ///     While Encryption Context Verification is a best practice, it is not
    ///     the topic of this example.
    /// </summary>
    private static void VerifyEncryptionContext(
        DecryptOutput decryptOutput,
        Dictionary<string, string> encryptionContext
    )
    {
        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var expectedPair in encryptionContext)
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
                throw new Exception("Encryption context does not match expected values");
    }

    /// <summary>
    ///     This helper method ensures the decrypted message is the same as the
    ///     encrypted message.
    /// </summary>
    private static void VerifyDecryptedIsPlaintext(DecryptOutput decryptOutput, MemoryStream plaintext)
    {
        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestDiscoveryFilterExample()
    {
        Run(GetPlaintextStream(), GetDefaultRegionKmsKeyArn(), GetAccountIds(), "aws");
    }
}
