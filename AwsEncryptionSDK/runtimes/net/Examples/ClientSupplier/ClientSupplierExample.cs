// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Amazon.KeyManagementService;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;
using static ExampleUtils.WriteExampleResources;

/// Demonstrates using a Custom Client Supplier.
/// See <c>RegionalRoleClientSupplier.cs</c> for the details of implementing a
/// custom client supplier.
/// This example uses an <c>AwsKmsMrkDiscoveryMultiKeyring</c>, but all
/// the AWS Multi Keyrings take Client Suppliers.
public class ClientSupplierExample
{
    private const string FILE_NAME = "defaultRegionMrkKey.bin";

    private static void Run(MemoryStream plaintext, List<string> accountIds, List<string> regions)
    {
        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        /* 1. Generate or load a ciphertext encrypted by the KMS Key. */
        // To focus on Client Suppliers, we will rely on a helper method
        // to provide the encrypted message (ciphertext).
        var ciphertext = ReadMessage(FILE_NAME);
        var encryptionContext = GetEncryptionContext();


        /* 2. Create a KMS Multi Keyring with the `RegionalRoleClientSupplier` */
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

        /* 3. Decrypt the ciphertext with created KMS Multi Keyring */
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

        /* 4. Verify the encryption context */
        VerifyEncryptionContext(decryptOutput, encryptionContext);

        /* 5. Verify the decrypted plaintext is the same as the original */
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);

        /* 6. Test the Missing Region Exception */
        // Demonstrate catching a custom exception.
        var createMultiFailed = false;
        createDecryptKeyringInput.Regions = new List<string>() {"fake-region"};
        try
        {
            materialProviders.CreateAwsKmsMrkDiscoveryMultiKeyring(createDecryptKeyringInput);
        }
        // Note that the exception returned is NOT a `MissingRegionException`
        catch (MissingRegionException)
        {
            throw;
        }
        // But is cast down to an `AwsCryptographicMaterialProvidersException`.
        catch (AwsCryptographicMaterialProvidersException exception)
        {
            // However, the message is as expected.
            Assert.Equal(
                "Region fake-region is not supported by this client supplier",
                exception.Message);
            createMultiFailed = true;
        }
        finally
        {
            Assert.True(createMultiFailed);
        }
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
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }

    // We test examples to ensure they remain up-to-date.
    // Example runs locally but commenting out for now to straighten out permissions
    // [Fact]
    // public void TestClientSupplierExample()
    // {
    //     if (!File.Exists(GetResourcePath(FILE_NAME)))
    //     {
    //         EncryptAndWrite(GetPlaintextStream(), GetDefaultRegionMrkKeyArn(), FILE_NAME);
    //     }
    //     Run(
    //         GetPlaintextStream(),
    //         GetAccountIds(),
    //         GetRegionIAMRoleMap().Keys.ToList()
    //     );
    // }
}
