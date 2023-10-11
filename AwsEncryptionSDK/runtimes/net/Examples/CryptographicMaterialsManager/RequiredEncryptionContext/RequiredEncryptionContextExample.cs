using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;
using static ExampleUtils.ExampleUtils;

/// Demonstrate an encrypt/decrypt cycle using a Required Encryption Context CMM.
/// A required encryption context CMM asks for required keys in the encryption context field
/// on encrypt such that they will not be stored on the message, but WILL be included in the header signature.
/// On decrypt the client MUST supply the key/value pair(s) that were not stored to successfully decrypt the message.
public class RequiredEncryptionContextExample
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
        // Create your required encryption context keys.
        // These keys MUST be in your encryption context.
        // These keys and their corresponding values WILL NOT be stored on the message but will be used
        // for authentication.
        var requiredEncryptionContextKeys = new List<string>()
        {
            "encryption",
            "but adds",
            "the data you are handling"
        };
        
        // Instantiate the Material Providers and the AWS Encryption SDK
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());

        // Create a keyring via a helper method.
        var keyring = GetRawAESKeyring(materialProviders);
        
        // Create a required encryption context cmm via a helper method.
        var cmm = GetRequiredEncryptionContextCMM(materialProviders, requiredEncryptionContextKeys, keyring);
        
        // Encrypt your plaintext data. NOTE: the keys "encryption", "but adds", and "the data you are handling"
        // WILL NOT be stored in the message header, but "is not" and "that can help you" WILL be stored.
        var encryptInput = new EncryptInput
        {
            Plaintext = plaintext,
            MaterialsManager = cmm,
            EncryptionContext = encryptionContext
        };
        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var ciphertext = encryptOutput.Ciphertext;
        
        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());
        
        // Attempt to decrypt your encrypted data using the same cryptographic material manager
        // you used on encrypt, but we won't pass the encryption context we DID NOT store on the message.
        // This will fail
        var decryptFailed = false;
        var decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            MaterialsManager = cmm,
        };
        try
        {
            encryptionSdk.Decrypt(decryptInput);
        }
        catch (AwsCryptographicMaterialProvidersException)
        {
            decryptFailed = true;
        }
        
        Assert.True(decryptFailed);
        
        // Decrypt your encrypted data using the same cryptographic material manager
        // you used to encrypt, but supply encryption context that contains ONLY the encryption context that
        // was NOT stored.
        var reproducedEcryptionContext = new Dictionary<string, string>()
        {
            {"encryption", "context"},
            {"but adds", "useful metadata"},
            {"the data you are handling", "is what you think it is"}
        };
        
        decryptInput = new DecryptInput
        {
            Ciphertext = ciphertext,
            MaterialsManager = cmm,
            EncryptionContext = reproducedEcryptionContext
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);

        VerifyDecryptedIsPlaintext(decryptOutput, plaintext);
    }
    
    private static void VerifyDecryptedIsPlaintext(DecryptOutput decryptOutput, MemoryStream plaintext)
    {
        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        var decrypted = decryptOutput.Plaintext;
        Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
    }
    
    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestRequiredEncryptionContextExample()
    {
        Run(GetPlaintextStream());
    }
}
