// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// One of the benefits of asymmetric encryption
// is that you can encrypt with just the public key.
// This means that you can give someone the ability to encrypt
// without giving them the ability to decrypt.
//
// The raw RSA keyring supports encrypt-only operations
// when it only has access to a public key.
//
// This example shows how to construct and use the raw RSA keyring
// to encrypt with only the public key and decrypt with the private key.
//
// If your RSA key is in PEM or DER format,
// see the ``keyring/raw_rsa/private_key_only_from_pem`` example.
//
// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-rsa-keyring
//
// In this example, we use the one-step encrypt and decrypt APIs.

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

using AWSEncryptionSDK;
using KeyringDefs;
using RawRSAKeyringDef;

// In this example, we use BouncyCastle to generate a wrapping key and handle conversions.
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.OpenSsl;

using ExampleUtils;
using Xunit;

// Demonstrate an encrypt/decrypt cycle using separate public and private raw RSA keyrings.
public class RawRSAKeyringPublicPrivateKeySeperateExample {
    static void Run(MemoryStream plaintext) {

        // Prepare your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        IDictionary<string, string> encryptionContext = new Dictionary<string, string>() {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // The key namespace and key name are defined by you
        // and are used by the raw RSA keyring to determine
        // whether it should attempt to decrypt an encrypted data key.
        //
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-rsa-keyring
        byte[] keyName = Encoding.UTF8.GetBytes("my RSA wrapping key");
        byte[] keyNamespace = Encoding.UTF8.GetBytes("some managed raw keys");

        // Generate an RSA private key to use with your keyring.
        // In practice, you should get this key from a secure key management system such as an HSM.
        //
        // The National Institute of Standards and Technology (NIST) recommends a minimum of 2048-bit keys for RSA.
        // https://www.nist.gov/publications/transitioning-use-cryptographic-algorithms-and-key-lengths
        int strength = 4096;

        // Create and initialize the key generator.
        SecureRandom secureRandom = new SecureRandom();
        RsaKeyPairGenerator keyGenerator = new RsaKeyPairGenerator();
        keyGenerator.Init(new KeyGenerationParameters(secureRandom, strength));

        // Generate a key pair.
        AsymmetricCipherKeyPair keygenPair = keyGenerator.GenerateKeyPair();

        // Extract the public key as a byte array.
        byte[] publicKeyBytes;
        using (var stringWriter = new StringWriter()) {
            var pemWriter = new PemWriter(stringWriter);
            pemWriter.WriteObject(keygenPair.Public);
            publicKeyBytes = Encoding.ASCII.GetBytes(stringWriter.ToString());
        }

        // Extract the private key as a byte array.
        byte[] privateKeyBytes;
        using (var stringWriter = new StringWriter()) {
            var pemWriter = new PemWriter(stringWriter);
            pemWriter.WriteObject(keygenPair.Private);
            privateKeyBytes = Encoding.ASCII.GetBytes(stringWriter.ToString());
        }

        // The keyring determines how your data keys are protected.
        //
        // Create the encrypt keyring that only has access to the public key.
        RawRSAKeyring publicKeyKeyring = Keyrings.MakeRawRSAKeyring(
                keyNamespace,
                keyName,
                // The wrapping algorithm tells the raw RSA keyring
                // how to use your wrapping key to encrypt data keys.
                //
                // We recommend using RSA_OAEP_SHA256_MGF1.
                // You should not use RSA_PKCS1 unless you require it for backwards compatibility.
                DafnyFFI.RSAPaddingModes.OAEP_SHA256,
                publicKeyBytes,
                null
                );

        // Create the decrypt keyring that has access to the private key.
        RawRSAKeyring privateKeyKeyring = Keyrings.MakeRawRSAKeyring(
                // The key namespace and key name MUST match the encrypt keyring.
                keyNamespace,
                keyName,
                // The wrapping algorithm MUST match the encrypt keyring.
                DafnyFFI.RSAPaddingModes.OAEP_SHA256,
                null,
                privateKeyBytes
                );

        // Encrypt your plaintext data using the encrypt keyring.
        MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(new AWSEncryptionSDK.Client.EncryptRequest{
                plaintext = plaintext,
                keyring = publicKeyKeyring,
                encryptionContext = encryptionContext
                });

        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

        // Try to decrypt your encrypted data using the *encrypt* keyring.
        // This demonstrates that you cannot decrypt using the public key.
        var exception = Assert.Throws<DafnyException>(() => AWSEncryptionSDK.Client.Decrypt(new AWSEncryptionSDK.Client.DecryptRequest{
                message = ciphertext,
                keyring = publicKeyKeyring
                }));
        Assert.Equal("Decryption key undefined", exception.Message);

        // Decrypt your encrypted data using the decrypt keyring.
        //
        // You do not need to specify the encryption context on decrypt
        // because the header of the encrypted message includes the encryption context.
        MemoryStream decrypted = AWSEncryptionSDK.Client.Decrypt(new AWSEncryptionSDK.Client.DecryptRequest{
                message = ciphertext,
                keyring = privateKeyKeyring
                });

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
    public void TestRawRSAKeyringPublicPrivateKeySeperateExample() {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
    }
}
