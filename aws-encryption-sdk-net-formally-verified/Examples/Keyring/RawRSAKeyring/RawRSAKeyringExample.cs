// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections.Generic;
using System.IO;

using Aws.Crypto;
using Aws.Esdk;

using Org.BouncyCastle.Security; // In this example, we use BouncyCastle to generate a wrapping key.
using Xunit;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;


/// Demonstrate an encrypt/decrypt cycle using a raw RSA keyring.
public class RawRSAKeyringExample {
    static void Run(MemoryStream plaintext) {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        Dictionary<string, string> encryptionContext = new Dictionary<string, string>() {
            {"name", "encryption context"},
            {"is_secret", "false"},
            {"is_public", "true"},
            {"purpose", "useful metadata"}
        };
    
        // Generate a 2,048 bit RSA Key to use with your keyring.
        // We generate a key with Bouncy Castle, but you could also load a key,
        // or generate a key with another low level cryptographic library.
        byte[] publicKeyBytes;
        byte[] privateKeyBytes;
        RSAEncryption.RSA.GenerateKeyPairBytes(2048, publicKeyBytes, privateKeyBytes);
        ibyteseq publicKey = byteseq.FromArray(publicKeyBytes);
        ibyteseq privateKey = byteseq.FromArray(privateKeyBytes);

        // The key namespace and key name are defined by you
        // and are used by the raw RSA keyring to determine
        // whether it should attempt to decrypt an encrypted data key.
        //
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-rsa-keyring
        string keyNamespace = "Some managed raw keys";
        string keyName = "My 2048-bit RSA wrapping key";

        // Create clients to access the Encryption SDK APIs.    
        // TODO: add client configuration objects
        IAwsCryptographicMaterialProviders materialProviders = new AwsCryptographicMaterialProvidersClient();
        IAwsEncryptionSdk encryptionSdkClient = new AwsEncryptionSdkClient();

        // Create the keyring that determines how your data keys are protected.
        CreateRawRsaKeyringInput createRawRsaKeyringInput = new CreateRawRsaKeyringInput
        {
            KeyNamespace = keyNamespace,
            KeyName = keyName,
            PaddingScheme = PaddingScheme.OAEP_SHA512_MGF1,
            PublicKey = publicKey,
            PrivateKey = privateKey
        };
        IKeyring keyring = materialProviders.CreateRawRsaKeyring(createRawRsaKeyringInput);

        // Create the materials manager that assembles cryptographic materials from your keyring.
        CreateDefaultCryptographicMaterialsManagerInput createMaterialsManagerInput =
            new CreateDefaultCryptographicMaterialsManagerInput {Keyring = keyring};
        ICryptographicMaterialsManager materialsManager =
            materialProviders.CreateDefaultCryptographicMaterialsManager(createMaterialsManagerInput);

        // Encrypt your plaintext data.
        EncryptInput encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = materialsManager,
            EncryptionContext = encryptionContext,
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
            MaterialsManager = materialsManager,
        };
        DecryptOutput decryptOutput = encryptionSdkClient.Decrypt(decryptInput);
        MemoryStream decrypted = decryptOutput.Plaintext;

        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());

        // Verify that the encryption context used in the decrypt operation includes
        // the encryption context that you specified when encrypting.
        // The AWS Encryption SDK can add pairs, so don't require an exact match.
        //
        // In production, always use a meaningful encryption context.
        // TODO: Add logic that checks the encryption context.        
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestRawRSAKeyringExample() {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
    }
}