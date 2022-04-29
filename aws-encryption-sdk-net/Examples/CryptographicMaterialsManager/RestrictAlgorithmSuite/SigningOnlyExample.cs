// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
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
        var materialProviders =
            AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
        var encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

        // Create a keyring via a helper method.
        var keyring = GetRawAESKeyring(materialProviders);

        // Create a DefaultCryptographicMaterialsManager
        var cmm = new SigningSuiteOnlyCMM(keyring, materialProviders);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = cmm,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
        };
        encryptInput.Validate(); // added to debug
        // The following line is throwing:
        /*
        Error Message:
        AWS.EncryptionSDK.AwsEncryptionSdkException : SigningSuiteOnlyCMM._GetEncryptionMaterials threw unexpected: System.Text.DecoderFallbackException: "Unable to translate bytes [80] at index 30 from specified code page to Unicode."
        Stack Trace:
        at AWS.EncryptionSDK.AwsEncryptionSdk._Encrypt(EncryptInput input) in /Volumes/workplace/Polymorph/aws-encryption-sdk-dafny/aws-encryption-sdk-net/Source/API/Generated/Esdk/AwsEncryptionSdk.cs:line 41
        at AWS.EncryptionSDK.AwsEncryptionSdkBase.Encrypt(EncryptInput input) in /Volumes/workplace/Polymorph/aws-encryption-sdk-dafny/aws-encryption-sdk-net/Source/API/Generated/Esdk/AwsEncryptionSdkBase.cs:line 16
        at SigningOnlyExample.Run(MemoryStream plaintext) in /Volumes/workplace/Polymorph/aws-encryption-sdk-dafny/aws-encryption-sdk-net/Examples/CryptographicMaterialsManager/RestrictAlgorithmSuite/SigningOnlyExample.cs:line 50
        at SigningOnlyExample.TestSigningOnlyExample() in /Volumes/workplace/Polymorph/aws-encryption-sdk-dafny/aws-encryption-sdk-net/Examples/CryptographicMaterialsManager/RestrictAlgorithmSuite/SigningOnlyExample.cs:line 155
        */
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
            AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
        };
        try
        {
            encryptionSdk.Encrypt(encryptInput);
        }
        catch (NonSigningSuiteException)
        {
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
            AlgorithmSuiteId = AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF,
            Keyring = keyring
        };
        encryptOutput = encryptionSdk.Encrypt(keyringEncryptInput);
        ciphertext = encryptOutput.Ciphertext;

        // Verify that the Signing Only CMM will fail decryption
        var decryptFailed = false;
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (NonSigningSuiteException)
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
        var path = GetEnvVariable("DYLD_LIBRARY_PATH");
        Console.Out.WriteLine(path);
        Run(GetPlaintextStream());
    }
}
