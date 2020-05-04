// This example shows how to configure and use a raw AES keyring.
//
// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-aes-keyring
//
// In this example, we use the encrypt and decrypt APIs.
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

using AWSEncryptionSDK;
using KeyringDefs;
using RawAESKeyringDef;

using Org.BouncyCastle.Security; // In this example, we use BouncyCastle to generate a wrapping key.

using ExampleUtils;
using Xunit;

namespace RawAESKeyringExample {
    /// Demonstrate an encrypt/decrypt cycle using a raw AES keyring.
    public class RawAESKeyringExample {
        static void Run(MemoryStream plaintext) {

            // Create your encryption context.
            // Remember that your encryption context is NOT SECRET.
            // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#encryption-context
            IDictionary<string, string> encryptionContext = new Dictionary<string, string>() {
                {"encryption", "context"},
                {"is not", "secret"},
                {"but adds", "useful metadata"},
                {"that can help you", "be confident that"},
                {"the data you are handling", "is what you think it is"}
            };

            // Generate a 256-bit AES key to use with your keyring.
            // Here we use BouncyCastle, but you don't have to.
            //
            // In practice, you should get this key from a secure key management system such as an HSM.
            byte[] key = GeneratorUtilities.GetKeyGenerator("AES256").GenerateKey();

            // The key namespace and key name are defined by you
            // and are used by the raw AES keyring to determine
            // whether it should attempt to decrypt an encrypted data key.
            //
            // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-aes-keyring
            byte[] keyName = Encoding.UTF8.GetBytes("My 256-bit AES wrapping key");
            byte[] keyNamespace = Encoding.UTF8.GetBytes("Some managed raw keys");

            // Create the keyring that determines how your data keys are protected.
            RawAESKeyring keyring = AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                    keyNamespace,
                    keyName,
                    key,
                    DafnyFFI.AESWrappingAlgorithm.AES_GCM_256
                    );

            // Encrypt your plaintext data.
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(new AWSEncryptionSDK.Client.EncryptRequest{
                    plaintext = plaintext,
                    keyring = keyring,
                    encryptionContext = encryptionContext
                    });

            // Demonstrate that the ciphertext and plaintext are different.
            Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

            // Decrypt your encrypted data using the same keyring you used on encrypt.
            // 
            // You do not need to specify the encryption context on decrypt
            // because the header of the encrypted message includes the encryption context.
            MemoryStream decrypted = AWSEncryptionSDK.Client.Decrypt(new AWSEncryptionSDK.Client.DecryptRequest{
                    message = ciphertext,
                    keyring = keyring
                    });

            // Demonstrate that the decrypted plaintext is identical to the original plaintext.
            Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
        }

        // We test examples to ensure they remain up-to-date.
        [Fact]
        public void TestRawAESKeyringExample() {
            Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
        }
    }
}
