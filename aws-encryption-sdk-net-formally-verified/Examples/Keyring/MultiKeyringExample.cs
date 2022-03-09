// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Aws.Crypto;
using Aws.Esdk;

using Org.BouncyCastle.Security;
using Org.BouncyCastle.Utilities; // In this example, we use BouncyCastle to generate a wrapping key.
using Xunit;

/// Demonstrate an encrypt/decrypt cycle using a Multi keyring consisting of an AWS KMS Keyring and
/// a raw AES keyring.
/// TODO: add KMS keyring
public class MultiKeyringExample {
    static void Run(MemoryStream plaintext) {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        Dictionary<string, string> encryptionContext = new Dictionary<string, string>() {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Create clients to access the Encryption SDK APIs.
        var materialProvidersClient = AwsCryptographicMaterialProvidersClientFactory.CreateDefaultAwsCryptographicMaterialProvidersClient();
        var encryptionSdkClient = AwsEncryptionSdkClientFactory.CreateDefaultAwsEncryptionSdkClient();
        
        // Create a KMS keyring to use as the generator
        // TODO

        // Create a raw AES keyring to additionally encrypt under
        IKeyring rawAESKeyring = CreateRawAESKeyring(materialProvidersClient);

        CreateMultiKeyringInput createMultiKeyringInput = new CreateMultiKeyringInput
        {
            Generator = rawAESKeyring,
            ChildKeyrings = Array.Empty<IKeyring>().ToList()
        };
        IKeyring multiKeyring = materialProvidersClient.CreateMultiKeyring(createMultiKeyringInput);

        // Encrypt your plaintext data.
        EncryptInput encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = rawAESKeyring,
            EncryptionContext = encryptionContext
        };
        EncryptOutput encryptOutput = encryptionSdkClient.Encrypt(encryptInput);
        MemoryStream ciphertext = encryptOutput.Ciphertext;

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Decrypt your encrypted data using the same keyring you used on encrypt.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        DecryptInput decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = rawAESKeyring,
        };
        DecryptOutput decryptOutput = encryptionSdkClient.Decrypt(decryptInput);

        // Before your application uses plaintext data, verify that the encryption context that
        // you used to encrypt the message is included in the encryption context that was used to
        // decrypt the message. The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        foreach (var (expectedKey, expectedValue) in encryptionContext)
        {
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedKey, out var decryptedValue)
                || !decryptedValue.Equals(expectedValue))
            {
                throw new System.Exception("Encryption context does not match expected values");
            }
        }

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        MemoryStream decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestMultiKeyringExample() {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
    }

    private static IKeyring CreateRawAESKeyring(IAwsCryptographicMaterialProvidersClient materialProvidersClient) {
        // Generate a 256-bit AES key to use with your keyring.
        // Here we use BouncyCastle, but you don't have to.
        //
        // In practice, you should get this key from a secure key management system such as an HSM.
        MemoryStream key = new MemoryStream(GeneratorUtilities.GetKeyGenerator("AES256").GenerateKey());

        // The key namespace and key name are defined by you
        // and are used by the raw AES keyring to determine
        // whether it should attempt to decrypt an encrypted data key.
        //
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-aes-keyring
        string keyNamespace = "Some managed raw keys";
        string keyName = "My 256-bit AES wrapping key";

        // Create the keyring that determines how your data keys are protected.
        CreateRawAesKeyringInput createAesKeyringInput = new CreateRawAesKeyringInput
        {
            KeyNamespace = keyNamespace,
            KeyName = keyName,
            WrappingKey = key,
            WrappingAlg = AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16,
        };
        IKeyring aesKeyring = materialProvidersClient.CreateRawAesKeyring(createAesKeyringInput);

        return aesKeyring;
    }
}
