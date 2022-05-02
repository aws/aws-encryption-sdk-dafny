// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Amazon;
using AWS.EncryptionSDK;
using AWS.EncryptionSDK.Core;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrates using a Custom Client Supplier.
/// See <c>RegionalRoleClientSupplier.cs</c> for the details of implementing a
/// custom client supplier.
/// This example uses an <c>AwsKmsMrkDiscoveryMultiKeyring</c>, but all
/// the AWS Multi Keyrings take Client Suppliers.
public class ClientSupplierExample
{
    private static void Run(MemoryStream plaintext, string keyArn, List<string> accountIds, List<string> regions)
    {
        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders =
            AwsCryptographicMaterialProvidersFactory.CreateDefaultAwsCryptographicMaterialProviders();
        var encryptionSdk = AwsEncryptionSdkFactory.CreateDefaultAwsEncryptionSdk();

        // To focus on Client Suppliers, we will rely on a helper method
        // to create the encrypted message (ciphertext).
        Dictionary<string, string> encryptionContext;
        MemoryStream ciphertext;
        (encryptionContext, ciphertext) = EncryptMessageWithKMSKey(
            plaintext, keyArn, materialProviders, encryptionSdk);


        // Now create a Discovery keyring to use for decryption.
        // We are passing in our Custom Client Supplier.
        var createDecryptKeyringInput = new CreateAwsKmsMrkDiscoveryMultiKeyringInput
        {
            ClientSupplier = new RegionalRoleClientSupplier(),
            Regions = regions,
            DiscoveryFilter = new DiscoveryFilter()
            {
                AccountIds = accountIds,
                Partition = "aws"
            }
        };

        // This is a Multi Keyring composed of MRK Discovery Keyrings.
        // All the keyrings have the same Discovery Filter.
        // Each keyring has its own KMS Client, which is provisioned by the Custom Client Supplier.
        var multiKeyring = materialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring(createDecryptKeyringInput);

        // On Decrypt, the header of the encrypted message (ciphertext) will be parsed.
        // The header contains the Encrypted Data Keys (EDKs), which, if the EDK
        // was encrypted by a KMS Keyring, includes the KMS Key arn.
        // For each member of the Multi Keyring, every EDK will try to be decrypted until a decryption is successful.
        // Since every member of the Multi Keyring is a MRK Discovery Keyring:
        //   Each Keyring will filter the EDKs by the Discovery Filter and the keyring's region.
        //      For each filtered EDK, the keyring will attempt decryption with the keyring's client.
        // All of this is done serially, until a success occurs or all keyrings have failed all (filtered) EDKs.
        // KMS MRK Discovery Keyrings will attempt to decrypt Multi Region Keys (MRKs) and regular KMS Keys.
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = multiKeyring
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);
        VerifyEncryptionContext(decryptOutput, encryptionContext);
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);

        // Demonstrate catching a custom exception.
        var createMultiFailed = false;
        createDecryptKeyringInput.Regions = new List<string>() {RegionEndpoint.CNNorth1.SystemName};
        try { materialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring(createDecryptKeyringInput); }
        // Note that the exception returned is NOT a `MissingRegionException`
        catch (MissingRegionException) { throw; }
        // But is cast down to an `AwsCryptographicMaterialProvidersBaseException`.
        catch (AwsCryptographicMaterialProvidersBaseException exception)
        {
            // However, the message is as expected.
            Assert.Equal(
                $"Region {RegionEndpoint.CNNorth1.SystemName} is not supported by this client supplier",
                exception.Message);
            createMultiFailed = true;
        }
        finally { Assert.True(createMultiFailed); }
    }


    /// <summary>
    ///     To focus on Client Suppliers, we rely on this helper method
    ///     to create the encrypted message (ciphertext) with the given KMS Key.
    /// </summary>
    private static (Dictionary<string, string> encryptionContext, MemoryStream ciphertext) EncryptMessageWithKMSKey(
        MemoryStream plaintext, string kmsKeyArn, IAwsCryptographicMaterialProviders materialProviders,
        IAwsEncryptionSdk encryptionSdk)
    {
        // Create your encryption context.
        // Remember that your encryption context is NOT SECRET.
        // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
        var encryptionContext = new Dictionary<string, string>
        {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        };

        // Create the keyring that determines how your data keys are protected.
        var createKeyringInput = new CreateAwsKmsMrkMultiKeyringInput()
        {
            Generator = kmsKeyArn,
            ClientSupplier = new RegionalRoleClientSupplier()
        };
        var encryptKeyring = materialProviders.CreateAwsKmsMrkMultiKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            Keyring = encryptKeyring,
            EncryptionContext = encryptionContext
        };
        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;
        return (encryptionContext, ciphertext);
    }

    /// <summary>
    ///     For this example, we break out the Encryption Context Verification
    ///     into a helper method.
    ///     While Encryption Context Verification is a best practice, it is not
    ///     the topic of this example.
    /// </summary>
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
            if (!decryptOutput.EncryptionContext.TryGetValue(expectedPair.Key, out var decryptedValue)
                || !decryptedValue.Equals(expectedPair.Value))
                throw new Exception("Encryption context does not match expected values");
    }

    /// <summary>
    ///     This is helper method that ensures the decrypted message is the
    ///     same as the encrypted message.
    /// </summary>
    private static void VerifyDecryptedIsPlaintext(DecryptOutput decryptOutput, MemoryStream plaintext)
    {
        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestClientSupplierExample()
    {
        Run(
            GetPlaintextStream(),
            GetDefaultRegionMrkKeyArn(),
            GetAccountIds(),
            GetRegionIAMRoleMap().Keys.ToList()
        );
    }
}
