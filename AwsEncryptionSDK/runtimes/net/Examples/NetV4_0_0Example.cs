// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections.Immutable;
using Amazon.KeyManagementService;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// This Demonstrates Allowing for or Forbidding the Decryption
/// of ESDK-NET v4.0.0 Messages.
/// It also documents the expected exceptions a
/// ESDK-NET v4.0.0 application would throw
/// if it encountered a proper ESDK Message,
/// like all those created by the ESDK-NET >= v4.0.1. 
/// 
/// The AWS Encryption SDK for .NET (ESDK-NET) v4.0.0
/// diverged from the Encryption SDK Message Specification.
///
/// The ESDK-NET v4.0.0,
/// when configured
/// with the Default Cryptographic Materials Manager
/// OR when configured with an Algorithm Suites with a Key Derivation Function (KDF)
/// but without Key Commitment,
/// created a Message Header Authentication Tag
/// that is secure but differs from the ESDK Message Specification.
/// 
/// By default, in ESDK-NET >= v4.0.1,
/// these divergent messages are read by identifying
/// a Header Authentication Tag failure and
/// recalculating the Header Authentication Tag
/// following the v4.0.0 behavior.
///
/// This retry can be disabled via the
/// NetV4_0_0_RetryPolicy,
/// an optional property of the
/// AwsEncryptionSdkConfig.
///
/// Distributed Applications may encounter these
/// Header Authentication Tag failures when
/// upgrading from ESDK-NET v4.0.0 to later ESDK-NET versions.
/// As the ESDK-NET v4.0.0 can,
/// for most ESDK Configurations,
/// only read messages it created,
/// and the ESDK-NET >= v4.0.1 cannot write 
/// such messages.
///
/// One path forward for distributed applications
/// is to catch these Exceptions,
/// which are documented in the ExpectedExceptions method below,
/// and delay processing of these messages until
/// the upgrade deployment is complete.
///
/// Please note that these exceptions MAY BE caused
/// by an ESDK-NET v4.0.0 upgrade,
/// or they can be caused by message tampering.
public class NetV4_0_0Example
{
    const string fileName = "v4DefaultRegionKmsKey.bin";
    private static readonly ImmutableDictionary<string, string> EncryptionContext = new Dictionary<string, string>
    {
        {"encryption", "context"},
        {"is not", "secret"},
        {"but adds", "useful metadata"},
        {"that can help you", "be confident that"},
        {"the data you are handling", "is what you think it is"}
    }.ToImmutableDictionary();

    private static void Run(
        MemoryStream plaintext,
        string keyArn
    )
    {
        /* 1. Instantiate the Material Providers and Encryption SDK */
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        // Instantiate the Encryption SDK such that it allows for 
        // ESDK-NET v4.0.0 messages to be decrypted.
        // This is the default configuration in v4.0.1 and later.
        var esdkConfig = new AwsEncryptionSdkConfig
        {
            NetV4_0_0_RetryPolicy = NetV4_0_0_RetryPolicy.ALLOW_RETRY
        };
        var encryptionSdk = new ESDK(esdkConfig);
        var keyringInput = new CreateAwsKmsKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = keyArn
        };
        var decryptKeyring = materialProviders.CreateAwsKmsKeyring(keyringInput);
        /* 3. Load an ESDK-NET v4.0.0 Message */
        var ciphertext = ReadMessage(fileName);
        Dictionary<string, string> encryptionContext = EncryptionContext.ToDictionary(p => p.Key, p => p.Value);
        
        /* 4. Decrypt the encrypted data. */
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            Keyring = decryptKeyring,
            EncryptionContext = encryptionContext
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        /* 5. Verify the decrypted plaintext is the original plaintext */
        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);
        
        /* 6. Instantiate another Encryption SDK that will reject ESDK-NET v4.0.0 Messages */
        encryptionSdk = new ESDK(new AwsEncryptionSdkConfig
        {
            NetV4_0_0_RetryPolicy = NetV4_0_0_RetryPolicy.FORBID_RETRY,
        });
        
        /* 7. Validate the ESDK rejects the Message with an Authentication error. */
        var decryptFailed = false;
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (AWS.Cryptography.Primitives.OpaqueError ex)
        {
            decryptFailed = true;
        }
        Assert.True(decryptFailed);
        ExpectedExceptions(decryptInput);
    }

    /// <summary>
    /// This method demonstrates the exceptions that
    /// are thrown by an ESDK-NET v4.0.0 application
    /// which decrypts proper ESDK Messages.
    /// 
    /// Such exceptions MAY BE caused by
    /// the differences between v4.0.0 and v4.0.1,
    /// though they CAN BE caused by other means. 
    /// </summary>
    private static void ExpectedExceptions(DecryptInput decryptInput)
    {
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig
        {
            NetV4_0_0_RetryPolicy = NetV4_0_0_RetryPolicy.FORBID_RETRY,
        });
        var decryptFailed = false;
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (AWS.Cryptography.Primitives.OpaqueError ex)
        {
            decryptFailed = true;
            Assert.True(ex.obj is Exception);
            switch (ex.obj)
            {
                case Org.BouncyCastle.Crypto.InvalidCipherTextException bc:
                    // On net48, BouncyCastle provides the AES-GCM cipher
                    Assert.Contains("mac check in GCM failed", bc.Message);
                    break;
                case System.Security.Cryptography.CryptographicException sys:
                    // On net6.0, the System's Cryptography provides the AES-GCM cipher
                    Assert.Contains(
                        "The computed authentication tag did not match the input authentication tag.", 
                        sys.Message);
                    break;
                default:
                    Assert.False(true,
                        "This is not a possible case," +
                        " unless the AES-GCM Cipher provider is unexpected.");
                    break;
            }
        }
        Assert.True(decryptFailed);
    }
    
    
    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestNetV4_0_0Example()
    {
        Run(GetPlaintextStream(), GetDefaultRegionKmsKeyArn());
    }
}
