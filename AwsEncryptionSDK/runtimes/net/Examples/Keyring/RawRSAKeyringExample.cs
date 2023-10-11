// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;

using Xunit;

/// Demonstrate an encrypt/decrypt cycle using a raw RSA keyring.
public class RawRSAKeyringExample
{
    // Used to test our example below.
    static string PRIVATE_KEY_PEM_FILENAME = "RSAKeyringExamplePrivateKey.pem";
    static string PUBLIC_KEY_PEM_FILENAME = "RSAKeyringExamplePublicKey.pem";

    private static void Run(MemoryStream plaintext, string publicKeyFileName, string privateKeyFileName)
    {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        var encryptionContext = new Dictionary<string, string>()
        {
            {"name", "encryption context"},
            {"is_secret", "false"},
            {"is_public", "true"},
            {"purpose", "useful metadata"}
        };

        // Get our PEM encoded RSA private and public keys
        var publicKey = new MemoryStream(System.IO.File.ReadAllBytes(publicKeyFileName));
        var privateKey = new MemoryStream(System.IO.File.ReadAllBytes(privateKeyFileName));

        // The key namespace and key name are defined by you
        // and are used by the raw RSA keyring to determine
        // whether it should attempt to decrypt an encrypted data key.
        //
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-rsa-keyring
        var keyNamespace = "Some managed raw keys";
        var keyName = "My 2048-bit RSA wrapping key";

        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // Create the keyring that determines how your data keys are protected.
        var createRawRsaKeyringInput = new CreateRawRsaKeyringInput
        {
            KeyNamespace = keyNamespace,
            KeyName = keyName,
            PaddingScheme = PaddingScheme.OAEP_SHA512_MGF1,
            PublicKey = publicKey,
            PrivateKey = privateKey
        };
        var keyring = materialProviders.CreateRawRsaKeyring(createRawRsaKeyringInput);

        // Encrypt your plaintext data.
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
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestRawRSAKeyringExample()
    {
        RSAEncryption.RSA.GenerateKeyPairBytes(2048, out var publicKeyBytes, out var privateKeyBytes);
        File.WriteAllBytes(PRIVATE_KEY_PEM_FILENAME, privateKeyBytes);
        File.WriteAllBytes(PUBLIC_KEY_PEM_FILENAME, publicKeyBytes);

        Run(ExampleUtils.ExampleUtils.GetPlaintextStream(),
            PUBLIC_KEY_PEM_FILENAME,
            PRIVATE_KEY_PEM_FILENAME);
    }
}
