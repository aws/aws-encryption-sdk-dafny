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
            RSAEncryption.PaddingMode paddingModeDafny = DafnyFFI.RSAPaddingModesToDafnyPaddingMode(paddingMode);
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

        // EncryptDecrypt is a helper method that performs an encrypt and then a decrypt on a plaintext that is
        // formatted using a given id. withParams dictates whether Encrypt should use any additional encryption parameters
        private string EncryptDecrypt(CMMDefs.CMM cmm, int id, bool withParams)
        {
            var plaintext = String.Format("Hello from id {0}", id);
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
            var encryptRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = plaintextStream, cmm = cmm};
            if (withParams) {
                encryptRequest.algorithmSuiteID = 0x0346;
                encryptRequest.frameLength = 2048;
            }
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(encryptRequest);
            MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(
                    new AWSEncryptionSDK.Client.DecryptRequest{message = ciphertext, cmm = cmm}
                    );
            StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
            String decoded = reader.ReadToEnd();
            return (plaintext == decoded) ? SUCCESS : String.Format("Id: {0} failed, decoded: {1}", id, decoded);
        }

        // EncryptDecryptThreaded is a helper method that calls EncryptDecrypt in a threaded manner using either 1 thread
        // if multithreading is disabled or 4 * the number of processors on the machine if it is enabled
        private void EncryptDecryptThreaded(CMMDefs.CMM cmm, bool isMultithreaded, bool withParams)
        {
            var concurrentBag = new ConcurrentBag<String>();
            var totalIds = isMultithreaded ? Environment.ProcessorCount * 4 : 1;
            // Sanity check that the total number of ids is valid
            Assert.True(isMultithreaded ? totalIds >= 4 : totalIds == 1);

            Parallel.For(
                0, totalIds, new ParallelOptions { MaxDegreeOfParallelism = totalIds },
                id => { concurrentBag.Add(EncryptDecrypt(cmm, id, withParams)); }
            );

            var totalDecoded = 0;
            foreach (string decoded in concurrentBag) {
                Assert.Equal(SUCCESS, decoded);
                totalDecoded += 1;
            }
            Assert.Equal(totalIds, totalDecoded);
        }

        // DefaultClientTestData represents simple client test data that does not require additional parameters outside of
        // whether the test should be multithreaded and whether it should use additional params for encrypt
        public static TheoryData<bool, bool> DefaultClientTestData
        {
            get
            {
                var data = new TheoryData<bool, bool>();
                var multithreadedList = new bool[] { true, false };
                var withParamsList = new bool[] { true, false };
                foreach (bool isMultithreaded in multithreadedList) {
                    foreach (bool withParams in withParamsList) {
                        data.Add(isMultithreaded, withParams);
                    }
                }
                return data;
            }
        }

        [Theory]
        [MemberData(nameof(DefaultClientTestData))]
        public void RoundTripHappyPath_KMS(bool isMultithreaded, bool withParams)
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
        }

        // RSAClientTestData represents client test data that can be used for simple RSA client tests that check all
        // combinations of RSAPaddingModes and DefaultClientTestData
        public static TheoryData<DafnyFFI.RSAPaddingModes, bool, bool> RSAClientTestData
        {
            get
            {
                var data = new TheoryData<DafnyFFI.RSAPaddingModes, bool, bool>();
                foreach (DafnyFFI.RSAPaddingModes paddingMode in Enum.GetValues(typeof(DafnyFFI.RSAPaddingModes))) {
                    foreach (var item in DefaultClientTestData) {
                        // Since this is just being used for unit tests, and we know DefaultClientTestData is
                        // TheoryData<bool, bool>, cast object to bool directly
                        data.Add(paddingMode, (bool) item[0], (bool) item[1]);
                    }
                }
                return data;
            }
        }

        [Theory]
        [MemberData(nameof(RSAClientTestData))]
        public void RoundTripHappyPath_RSA(DafnyFFI.RSAPaddingModes paddingMode, bool isMultithreaded, bool withParams)
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithRSAKeyring(paddingMode);
            EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
        }

        // AESClientTestData represents client test data that can be used for simple AES client tests that check all
        // combinations of AESWrappingAlgorithm and DefaultClientTestData
        public static TheoryData<DafnyFFI.AESWrappingAlgorithm, bool, bool> AESClientTestData
        {
            get
            {
                var data = new TheoryData<DafnyFFI.AESWrappingAlgorithm, bool, bool>();
                foreach (DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm in Enum.GetValues(typeof(DafnyFFI.AESWrappingAlgorithm))) {
                    foreach (var item in DefaultClientTestData) {
                        // Since this is just being used for unit tests, and we know DefaultClientTestData is
                        // TheoryData<bool, bool>, cast object to bool directly
                        data.Add(wrappingAlgorithm, (bool) item[0], (bool) item[1]);
                    }
                }
                return data;
            }
        }

        [Theory]
        [MemberData(nameof(AESClientTestData))]
        public void RoundTripHappyPath_AES(DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm, bool isMultithreaded, bool withParams)
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithAESKeyring(wrappingAlgorithm);
            EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
        }

        [Theory]
        [MemberData(nameof(DefaultClientTestData))]
        public void RoundTripHappyPath_MultiKeyring(bool isMultithreaded, bool withParams)
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithMultiKeyring();
            EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
        }
        
        [Fact]
        public void EncryptNullPlaintext()
        {
            var cmm = MakeDefaultCMMWithKMSKeyring();
            var nullRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = null, cmm = cmm};

            Assert.Throws<ArgumentNullException>(() =>
            AWSEncryptionSDK.Client.Encrypt(nullRequest));
        } 

        [Fact]
        public void EncryptNullCMMKeyring()
        {
            var nullRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream()};

            Assert.Throws<ArgumentNullException>(() =>
            AWSEncryptionSDK.Client.Encrypt(nullRequest));
        }

        [Fact]
        public void EncryptCMMKeyringOverload()
        {
            var tooMuch = new AWSEncryptionSDK.Client.EncryptRequest{
                plaintext = new MemoryStream(),
                cmm = MakeDefaultCMMWithKMSKeyring(),
                keyring = MakeKMSKeyring()
            };

            Assert.Throws<ArgumentException>(() =>
            AWSEncryptionSDK.Client.Encrypt(tooMuch));
        }

        [Fact]
        public void EncryptNullEncryptionContext()
        {
            var nullCtx = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream(), keyring = MakeKMSKeyring(), encryptionContext = null};

            Assert.Throws<ArgumentNullException>(() =>
            AWSEncryptionSDK.Client.Encrypt(nullCtx));
        }

        [Fact]
        public void EncryptBadAlgorithSuiteID()
        {
            var badRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream(), keyring = MakeKMSKeyring(), algorithmSuiteID = 1};

            Assert.Throws<ArgumentException>(() =>
            AWSEncryptionSDK.Client.Encrypt(badRequest));
        }

        [Fact]
        public void EncryptFrameLengthZero()
        {
            var badRequest = new AWSEncryptionSDK.Client.EncryptRequest{plaintext = new MemoryStream(), keyring = MakeKMSKeyring(), frameLength = 0};

            var exception = Assert.Throws<DafnyException>(() =>
            AWSEncryptionSDK.Client.Encrypt(badRequest));

            Assert.Equal("Request frameLength must be > 0", exception.Message);
        }

        [Fact]
        public void EncryptInvalidEncryptionContextKeys()
        {
            var badRequest = new AWSEncryptionSDK.Client.EncryptRequest{
                plaintext = new MemoryStream(),
                keyring = MakeKMSKeyring(),
                encryptionContext = new Dictionary<string, string>(){{"aws-crypto-public-key", "this string does not matter"}}
            };

            var exception = Assert.Throws<DafnyException>(() =>
            AWSEncryptionSDK.Client.Encrypt(badRequest));

            Assert.Equal("Invalid encryption context keys.", exception.Message);
        }

        [Fact]
        public void DecryptNullMessage()
        {
            var badRequest = new AWSEncryptionSDK.Client.DecryptRequest{message = null};

            Assert.Throws<ArgumentNullException>(() =>
            AWSEncryptionSDK.Client.Decrypt(badRequest));
        }
        
        [Fact]
        public void DecryptNullCMMKeyring()
        {
            var nullRequest = new AWSEncryptionSDK.Client.DecryptRequest{message = new MemoryStream()};

            Assert.Throws<ArgumentNullException>(() =>
            AWSEncryptionSDK.Client.Decrypt(nullRequest));
        }

        [Fact]
        public void DecryptCMMKeyringOverload()
        {
            var tooMuch = new AWSEncryptionSDK.Client.DecryptRequest{
                message = new MemoryStream(),
                cmm = MakeDefaultCMMWithKMSKeyring(),
                keyring = MakeKMSKeyring()
            };

            Assert.Throws<ArgumentException>(() =>
            AWSEncryptionSDK.Client.Decrypt(tooMuch));
        }

        // TODO-RS: Test for nulls and other Dafny requirement violations
    }
}
