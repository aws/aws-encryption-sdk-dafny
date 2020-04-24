using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

using AWSEncryptionSDK;
using KeyringDefs;
using RawAESKeyringDef;

using ExampleUtils;

using Org.BouncyCastle.Security;
using Xunit;

namespace RawAESKeyringExample {
    public class RawAESKeyringExample {
        static void Run(MemoryStream plaintext) {

            // Generate a 256-bit AES key to use with your keyring.
            // Here we use BouncyCastle, but you don't have to.
            byte[] key = GeneratorUtilities.GetKeyGenerator("AES256").GenerateKey();

            // Key name, and key namespace are defined by you,
            // and are used by the raw AES keyring to determine
            // whether it should attempt to decrypt an encrypted data key.
            byte[] keyName = Encoding.UTF8.GetBytes("My 256-bit AES wrapping key");
            byte[] keyNamespace = Encoding.UTF8.GetBytes("Some managed raw keys");

            // Create the keyring that determines how your data keys are protected.
            RawAESKeyring keyring = AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                    keyNamespace,
                    keyName,
                    key,
                    DafnyFFI.AESWrappingAlgorithm.AES_GCM_256
                    );

            // Create your encryption context.
            // Remember that you encryption context is NOT SECRET.
            IDictionary<string, string> encryptionContext = new Dictionary<string, string>() {
                {"encryption", "context"},
                {"is not", "secret"},
                {"but adds", "useful metadata"},
                {"that can help you", "be confident that"},
                {"the data you are handling", "is what you think it is"}
            };

            // Encrypt your data.
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(new AWSEncryptionSDK.Client.EncryptRequest{
                    plaintext = plaintext,
                    keyring = keyring,
                    encryptionContext = encryptionContext
                    });

            // Demonstrate that the ciphertext and plaintext are different.
            Assert.NotEqual(ciphertext.ToArray(), plaintext.ToArray());

            // Decrypt your data.
            // 
            // Your encryption context is contained in the header of the ciphertext,
            // so you don't need to provide it again.
            MemoryStream decrypted = AWSEncryptionSDK.Client.Decrypt(new AWSEncryptionSDK.Client.DecryptRequest{
                    message = ciphertext,
                    keyring = keyring
                    });

            Assert.Equal(decrypted.ToArray(), plaintext.ToArray());
        }

        // Test examples to ensure they remain up-to-date.
        [Fact]
        public void TestRawAESKeyringExample() {
            Run(ExampleUtils.ExampleUtils.GetPlaintextStream());
        }
    }
}
