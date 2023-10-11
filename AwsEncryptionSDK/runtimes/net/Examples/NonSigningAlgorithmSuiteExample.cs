// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using AWS.Cryptography.MaterialProviders;
using AWS.Cryptography.EncryptionSDK;
using Org.BouncyCastle.Security; // In this example, we use BouncyCastle to generate a wrapping key.
using Xunit;

/// Demonstrate an encrypt/decrypt cycle using a raw AES keyring and a non-signing Algorithm Suite.
/// This also demonstrates how to customize the Algorithm Suite used to encrypt the plaintext.
/// For a full list of the Algorithm Suites the Encryption SDK supports,
/// see https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/algorithms-reference.html
public class NonSigningAlgorithmSuiteExample
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

        // Generate a 256-bit AES key to use with your keyring.
        // Here we use BouncyCastle, but you don't have to.
        //
        // In practice, you should get this key from a secure key management system such as an HSM.
        var key = new MemoryStream(GeneratorUtilities.GetKeyGenerator("AES256").GenerateKey());

        // The key namespace and key name are defined by you
        // and are used by the raw AES keyring to determine
        // whether it should attempt to decrypt an encrypted data key.
        //
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-aes-keyring
        var keyNamespace = "Some managed raw keys";
        var keyName = "My 256-bit AES wrapping key";

        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // Create the keyring that determines how your data keys are protected.
        var createKeyringInput = new CreateRawAesKeyringInput
        {
            KeyNamespace = keyNamespace,
            KeyName = keyName,
            WrappingKey = key,
            // This is the algorithm that will encrypt the Data Key.
            // It is different from the Algorithm Suite.
            WrappingAlg = AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16
        };
        var keyring = materialProviders.CreateRawAesKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = keyring,
            EncryptionContext = encryptionContext,
            // Here, we customize the Algorithm Suite that is used to Encrypt the plaintext.
            // In particular, we use an Algorithm Suite without Signing.
            // Signature verification adds a significant performance cost on decryption.
            // If the users encrypting data and the users decrypting data are equally trusted,
            // consider using an algorithm suite that does not include signing.
            // See more about Digital Signatures:
            // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#digital-sigs
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
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
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestNonSigningAlgorithmSuiteExample()
    {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
    }
}
