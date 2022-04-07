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

/// Demonstrate an encrypt/decrypt cycle using a Multi-Keyring made up of multiple AWS KMS
/// MRK Keyrings.
public class AwsKmsMrkMultiKeyringExample
{
    // For this example, `mrkKeyArn` is the ARN for a MRK KMS Key located in your default region,
    // and `kmsKeyArn` is the ARN for a KMS Key, possibly located in a different Region than the MRK Key.
    // Finally, `mrkReplicaKeyArn` is an Arn for a KMS MRK key that
    // is a replica of the `mkrKeyArn` in a different Region.
    private static void Run(MemoryStream plaintext, string mrkKeyArn, string kmsKeyArn, string mrkReplicateKeyArn)
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

        // Create an AwsKmsMrkMultiKeyring that protects your data under two different KMS Keys.
        // The Keys can either be regular KMS Keys or MRK Keys.
        // Either KMS Key individually is capable of decrypting data encrypted under this keyring.
        var createAwsKmsMultiKeyringInput = new CreateAwsKmsMrkMultiKeyringInput
        {
            Generator = mrkKeyArn,
            KmsKeyIds = new List<string>() {kmsKeyArn}
        };
        var kmsMultiKeyring = materialProviders.CreateAwsKmsMrkMultiKeyring(createAwsKmsMultiKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = kmsMultiKeyring,
            EncryptionContext = encryptionContext
        };

        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Decrypt your encrypted data using the AwsKmsMrkMultiKeyring.
        // It will decrypt the data using the generator KMS key since
        // it is the first available KMS key on the keyring that
        // is capable of decrypting the data.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = kmsMultiKeyring
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

        // Demonstrate that a single AwsKmsMrkKeyring configured with either KMS key or the replica
        // is also capable of decrypting the data.
        //
        // Create a single AwsKmsMrkKeyring with the replica KMS MRK key from our second region.
        var createKeyringInput = new CreateAwsKmsMrkKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(GetRegionEndpointFromArn(mrkReplicateKeyArn)),
            KmsKeyId = mrkReplicateKeyArn
        };
        var mrkReplicateKeyring = materialProviders.CreateAwsKmsMrkKeyring(createKeyringInput);

        // Decrypt your encrypted data using the AwsKmsKeyring configured with the KMS Key from the second region.
        var kmsKeyringDecryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = mrkReplicateKeyring
        };
        var kmsKeyringDecryptOutput = encryptionSdk.Decrypt(kmsKeyringDecryptInput);

        // Verify the Encryption Context on the output
        foreach (var expectedPair in encryptionContext)
        {
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var kmsKeyringDecrypted = kmsKeyringDecryptOutput.Plaintext;
        Assert.Equal(kmsKeyringDecrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsMrkMultiKeyringExample()
    {
        Run(
            GetPlaintextStream(),
            GetDefaultRegionMrkKeyArn(),
            GetDefaultRegionKmsKeyArn(),
            GetAlternateRegionMrkKeyArn()
        );
    }
}
