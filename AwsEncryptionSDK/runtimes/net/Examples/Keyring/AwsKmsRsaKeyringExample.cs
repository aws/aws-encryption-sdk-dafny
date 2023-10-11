
using System.Text;
using Amazon.KeyManagementService;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Xunit;

/// Demonstrate an encrypt/decrypt cycle using an AWS KMS RSA keyring.
public class AwsKmsRsaKeyringExample
{
    // THIS IS A PUBLIC RESOURCE. DO NOT USE IN A PRODUCTION ENVIRONMENT.
    private static readonly string kmsRsaKeyArn = "arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297";
    
    private static void Run(MemoryStream getPlaintextStream, MemoryStream kmsRsaPublicKey)
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
        var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
        var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());
        
        // Create the keyring that determines how your data keys are protected.
        var createKeyringInput = new CreateAwsKmsRsaKeyringInput
        {
            KmsClient = new AmazonKeyManagementServiceClient(),
            KmsKeyId = kmsRsaKeyArn,
            PublicKey = kmsRsaPublicKey,
            EncryptionAlgorithm = EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256
        };

        var kmsRsaKeyring = materialProviders.CreateAwsKmsRsaKeyring(createKeyringInput);

        // Encrypt your plaintext data.
        var encryptInput = new EncryptInput
        {
            Plaintext = getPlaintextStream,
            Keyring = kmsRsaKeyring,
            EncryptionContext = encryptionContext,
            AlgorithmSuiteId = ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
        };

        var encryptOutput = encryptionSdk.Encrypt(encryptInput);
        var cipherText = encryptOutput.Ciphertext;
        
        // Demonstrate that the ciphertext and plaintext are different.
        Assert.NotEqual(cipherText.ToArray(), getPlaintextStream.ToArray());

        // Decrypt your encrypted data using the same keyring you used on encrypt.
        var decryptInput = new DecryptInput
        {
            Ciphertext = cipherText,
            Keyring = kmsRsaKeyring
        };
        var decryptOutput = encryptionSdk.Decrypt(decryptInput);
        var decrypted = decryptOutput.Plaintext;
        
        // Demonstrate that the decrypted plaintext is identical to the original plaintext.
        Assert.Equal(decrypted.ToArray(), getPlaintextStream.ToArray());
    }
    
    // We test examples to ensure they remain up-to-date.
    [Fact]
    public void TestAwsKmsRsaKeyringExample()
    {
        Run(ExampleUtils.ExampleUtils.GetPlaintextStream(), ExampleUtils.ExampleUtils.GetKmsRSAPublicKey());
    }

}
