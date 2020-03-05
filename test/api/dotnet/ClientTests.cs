using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using KeyringDefs;
using KMSUtils;
using Org.BouncyCastle.Security;
using Xunit;

namespace AWSEncryptionSDKTests
{
    public class ClientTests
    {

        private static string SUCCESS = "SUCCESS";

        // MakeKMSKeyring is a helper method that creates a KMS Keyring for unit testing
        private Keyring MakeKMSKeyring()
        {
            String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
            ClientSupplier clientSupplier = new DefaultClientSupplier();
            return AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());
        }

        // MakeDefaultCMMWithKMSKeyring is a helper method that creates a default CMM using a KMS Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithKMSKeyring()
        {
            Keyring keyring = MakeKMSKeyring();
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // MakeRSAKeyring is a helper method that creates a RSA Keyring for unit testing
        private Keyring MakeRSAKeyring(DafnyFFI.RSAPaddingModes paddingMode)
        {
            // MakeRawRSAKeyring expects DafnyFFI.RSAPaddingModes while GenerateKeyPairBytes expects
            // RSAEncryption.PaddingMode
            RSAEncryption.PaddingMode paddingModeDafny = paddingMode switch {
                DafnyFFI.RSAPaddingModes.PKCS1 => RSAEncryption.PaddingMode.create_PKCS1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA1 => RSAEncryption.PaddingMode.create_OAEP__SHA1(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA256 => RSAEncryption.PaddingMode.create_OAEP__SHA256(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA384 => RSAEncryption.PaddingMode.create_OAEP__SHA384(),
                DafnyFFI.RSAPaddingModes.OAEP_SHA512 => RSAEncryption.PaddingMode.create_OAEP__SHA512(),
                _ => throw new ArgumentException("Unsupported RSA Padding Mode")
            };
            byte[] publicKey;
            byte[] privateKey;
            RSAEncryption.RSA.GenerateKeyPairBytes(2048, paddingModeDafny, out publicKey, out privateKey);

            return AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
                Encoding.UTF8.GetBytes("namespace"),
                Encoding.UTF8.GetBytes("myKeyring"),
                paddingMode,
                publicKey,
                privateKey);
        }

        // MakeDefaultCMMWithRSAKeyring is a helper method that creates a default CMM using a RSA Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithRSAKeyring(DafnyFFI.RSAPaddingModes paddingMode)
        {
            Keyring keyring = MakeRSAKeyring(paddingMode);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // MakeAESKeyring is a helper method that creates an AES Keyring for unit testing
        private Keyring MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            // For our unit tests, we can just generate an AES 256 key
            var keygen = GeneratorUtilities.GetKeyGenerator("AES256");
            var wrappingKey = keygen.GenerateKey();

            return AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                Encoding.UTF8.GetBytes("namespace"),
                Encoding.UTF8.GetBytes("myKeyring"),
                wrappingKey,
                wrappingAlgorithm);
        }

        // MakeDefaultCMMWithAESKeyring is a helper method that creates a default CMM using an AES Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithAESKeyring(DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            Keyring keyring = MakeAESKeyring(wrappingAlgorithm);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // MakeDefaultCMMWithMultiKeyring is a helper method that creates a default CMM using a Multi-Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithMultiKeyring()
        {
            Keyring generator = MakeKMSKeyring();
            Keyring[] children = new Keyring[] {
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.PKCS1),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA1),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA256),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA384),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA512),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_128),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_192),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_256)
            };

            Keyring keyring = AWSEncryptionSDK.Keyrings.MakeMultiKeyring(generator, children);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // DecodeMemoryStream is a helper method that takes a MemoryStream ciphertext and decrypts it
        private String DecodeMemoryStream(MemoryStream ciphertext, CMMDefs.CMM cmm)
        {
            MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertext, cmm);
            StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
            return reader.ReadToEnd();
        }

        // EncryptDecrypt is a helper method that performs an encrypt and then a decrypt on a plaintext that is
        // formatted using a given id. withParams dictates whether Encrypt should use any additional encryption parameters
        private string EncryptDecrypt(CMMDefs.CMM cmm, int id, bool withParams)
        {
            var plaintext = String.Format("Hello from id {0}", id);
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
            MemoryStream ciphertext = withParams
                ? AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>(), 0x0346, 2048)
                : AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);
            String decoded = DecodeMemoryStream(ciphertext, cmm);
            return (plaintext == decoded) ? SUCCESS : String.Format("Id: {0} failed, decoded: {1}", id, decoded);
        }

        [Fact]
        public void RoundTripHappyPath()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            String response = EncryptDecrypt(cmm, 0, false);
            Assert.Equal(SUCCESS, response);
        }

        [Fact]
        public void RoundTripHappyPathWithParams()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            String response = EncryptDecrypt(cmm, 0, true);
            Assert.Equal(SUCCESS, response);
        }

        // EncryptDecryptMultiThreaded is a helper method that calls EncryptDecrypt in a threaded manner using
        // 4 * the number of processors on the machine
        private void EncryptDecryptMultiThreaded(CMMDefs.CMM cmm, bool withParams)
        {
            var concurrentBag = new ConcurrentBag<String>();
            var totalIds = Environment.ProcessorCount * 4;
            // Sanity check that the total number of ids is valid
            Assert.True(totalIds >= 4);

            Parallel.For(
                0, totalIds,
                id => { concurrentBag.Add(EncryptDecrypt(cmm, id, withParams)); }
            );

            var totalDecoded = 0;
            foreach (string decoded in concurrentBag) {
                Assert.Equal(SUCCESS, decoded);
                totalDecoded += 1;
            }
            Assert.Equal(totalIds, totalDecoded);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_KMS()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_KMS_Params()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_PKCS1()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.PKCS1;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_PKCS1_Params()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.PKCS1;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA1()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA1;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA1_Params()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA1;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA256()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA256;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA256_Params()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA256;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA384()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA384;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA384_Params()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA384;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA512()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA512;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_RSA_OAEP_SHA512_Params()
        {
            DafnyFFI.RSAPaddingModes paddingMode = DafnyFFI.RSAPaddingModes.OAEP_SHA512;
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_128()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_128;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_128_Params()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_128;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_192()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_192;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_192_Params()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_192;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_256()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_256;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_AES_GCM_256_Params()
        {
            DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm = DafnyFFI.AESWrappingAlgorithm.AES_GCM_256;
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptMultiThreaded(cmm, true);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_MultiKeyring()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithMultiKeyring();
            EncryptDecryptMultiThreaded(cmm, false);
        }

        [Fact]
        public void RoundTripHappyPathThreaded_MultiKeyring_Params()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithMultiKeyring();
            EncryptDecryptMultiThreaded(cmm, true);
        }
    }
}
