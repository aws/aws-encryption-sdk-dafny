// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using Amazon;
using Amazon.KeyManagementService;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;
using static ExampleUtils.WriteExampleResources;

/// Demonstrate decryption using an AWS KMS Multi-Region Key (MRK) discovery keyring.
public class AwsKmsMrkDiscoveryKeyringExample
{
    private const string FILE_NAME = "defaultRegionMrkKey.bin";

    private static void Run(MemoryStream plaintext, RegionEndpoint decryptRegion)
    {
        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // To focus on the AWS KMS MRK Discovery Keyring,
        // we will rely on a helper method
        // to provide the encrypted message (ciphertext).
        var ciphertext = ReadMessage(FILE_NAME);
        var encryptionContext = GetEncryptionContext();

        // Now create a Discovery keyring to use for decryption.
        // In order to illustrate the MRK behavior of this keyring, we configure
        // the keyring to use the second KMS region where the MRK is replicated to.
        var createDecryptKeyringInput = new CreateAwsKmsMrkDiscoveryKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(decryptRegion),
            Region = decryptRegion.SystemName,
            DiscoveryFilter = new DiscoveryFilter()
            {
                AccountIds = GetAccountIds(),
                Partition = "aws"
            }
        };
        var decryptKeyring = materialProviders.CreateAwsKmsMrkDiscoveryKeyring(createDecryptKeyringInput);

        // On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
        // The header contains the Encrypted Data Keys (EDKs), which, if the EDK
        // was encrypted by a KMS Keyring, includes the KMS Key ARN.
        // The MRK Discovery Keyring filters these EDKs for:
        // - EDKs encrypted by Single Region KMS Keys in the keyring's region
        // OR
        // - EDKs encrypted by Multi Region KMS Keys
        // Additionally, the keyring filters these KMS encrypted data keys
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
        if (!File.Exists(GetResourcePath(FILE_NAME)))
        {
            EncryptAndWrite(GetPlaintextStream(), GetDefaultRegionMrkKeyArn(), FILE_NAME);
        }
        Run(
            GetPlaintextStream(),
            GetRegionEndpointFromArn(GetAlternateRegionMrkKeyArn())
        );
    }
}
