// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrate an encrypt/decrypt cycle using a Custom Cryptographic Materials Manager (CMM).
/// `SigningSuiteOnlyCMM.cs` demonstrates creating a custom CMM to reject Non-Signing Algorithms.
public class SigningOnlyExample
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

        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // Create a keyring via a helper method.
        var keyring = GetRawAESKeyring(materialProviders);

        // Create an instance of the custom CMM
        var cmm = new SigningSuiteOnlyCMM(keyring, materialProviders);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = cmm,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
        };
        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Decrypt your encrypted data using the same cryptographic material manager
        // you used on encrypt.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            MaterialsManager = cmm
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        VerifyEncryptionContext(decryptOutput, encryptionContext);
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);

        // Demonstrate that a Non Signing Algorithm Suite will be rejected
        // by the CMM.
        var encryptFailed = false;
        encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = cmm,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
        };
        try
        {
            encryptionSdk.Encrypt(encryptInput);
        }
        // The Encryption SDK converts the custom exception
        // to an AwsCryptographicMaterialProvidersException, while retaining
        // the exception message.
        catch (AwsCryptographicMaterialProvidersException baseException)
        {
            Assert.Equal("Algorithm Suite must use Signing", baseException.Message);
            encryptFailed = true;
        }

        Assert.True(encryptFailed);

        // Demonstrate that a message encrypted with a Non-Signing Algorithm
        // will also be rejected.

        // Create an encrypted message with a Non-Signing Algorithm.
        // Here, we do not use the Signing Only CMM, but just pass a Keyring.
        // The Encryption SDK will then create a Default CMM to facilitate the
        // assembling and checking the cryptographic materials.
        var keyringEncryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY,
            Keyring = keyring
        };
        encryptOutput = encryptionSdk.Encrypt(keyringEncryptInput);
        ciphertext = encryptOutput.Ciphertext;
        decryptInput.Ciphertext = ciphertext;

        // Verify that the Signing Only CMM will fail decryption
        var decryptFailed = false;
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
        {
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
            {
                throw new Exception("Encryption context does not match expected values");
            }
        }
    }

    private static void VerifyDecryptedIsPlaintext(DecryptOutput decryptOutput, MemoryStream plaintext)
    {
        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestSigningOnlyExample()
    {
        Run(GetPlaintextStream());
    }
}
