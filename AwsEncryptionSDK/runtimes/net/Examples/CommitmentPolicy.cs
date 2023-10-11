// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrates setting the commitment policy.
/// The commitment policy is a security feature that, if set to its strictest
/// setting, ensures that messages are decrypted with the same data key
/// used to encrypt them.
/// Read more about Key Commitment and the commitment policy Here:
/// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#key-commitment
public class CommitmentPolicyExample
{
    private static void Run(MemoryStream plaintext)
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
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        // Set the EncryptionSDK's commitment policy parameter
        var esdkConfig = new AwsEncryptionSdkConfig
        {
            CommitmentPolicy = ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT
        };
        // Instantiate the EncryptionSDK with the configuration
        var encryptionSdk = new ESDK(esdkConfig);

        // For illustrative purposes we create a Raw AES Keyring. You can use any keyring in its place.
        var keyring = GetRawAESKeyring(materialProviders);

        // Encrypt your plaintext data.
        // Since the CommitmentPolicy is set to Forbid Encrypt,
        // the Encryption SDK will encrypt the plaintext without key commitment.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = keyring,
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
            Keyring = keyring
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

        // Demonstrate that an EncryptionSDK that enforces Key Commitment on Decryption
        // will fail to decrypt the encrypted message (as it was encrypted without Key Commitment).
        var failedDecryption = false;
        esdkConfig = new AwsEncryptionSdkConfig
        {
            CommitmentPolicy = ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT
        };
        // Instantiate the EncryptionSDK with the configuration
        encryptionSdk = new ESDK(esdkConfig);

        // Repeat the earlier decryption steps, proving that they fail
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
#pragma warning disable 168
        catch (InvalidAlgorithmSuiteInfoOnDecrypt ignore)
#pragma warning restore 168
        {
            failedDecryption = true;
        }
        Assert.True(failedDecryption);

        // Demonstrate that the EncryptionSDK will not allow the commitment policy
        // and the Algorithm Suite to be in conflict.
        var failedEncrypt = false;
        // Now, the `encryptionSDK` is configured to Require Key Commitment
        // on both Encrypt and Decrypt (this was set on lines 100 - 105).
        // If we try and Encrypt data with an Algorithm that does not support Commitment:
        encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = keyring,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
        };
        // The encryption will fail.
        try
        {
            encryptionSdk.Encrypt(encryptInput);
        }
#pragma warning disable 168
        catch (InvalidAlgorithmSuiteInfoOnEncrypt ignore)
#pragma warning restore 168
        {
            failedEncrypt = true;
        }
        Assert.True(failedEncrypt);
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestCommitmentPolicyExample()
    {
        Run(GetPlaintextStream());
    }
}
