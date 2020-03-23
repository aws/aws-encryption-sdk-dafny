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
        private static string KEYRING_NAMESPACE = "namespace";
        private static string KEYRING_NAME = "myKeyring";

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
        private Keyring MakeRSAKeyring(DafnyFFI.RSAPaddingModes paddingMode, String nameSpace, String name)
        {
            // MakeRawRSAKeyring expects DafnyFFI.RSAPaddingModes while GenerateKeyPairBytes expects
            // RSAEncryption.PaddingMode
            RSAEncryption.PaddingMode paddingModeDafny = DafnyFFI.RSAPaddingModesToDafnyPaddingMode(paddingMode);
            byte[] publicKey;
            byte[] privateKey;
            RSAEncryption.RSA.GenerateKeyPairBytes(2048, paddingModeDafny, out publicKey, out privateKey);
            // If namespace or name is null, just pass null into the constructor to properly test this behavior
            return AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
                nameSpace == null ? null : Encoding.UTF8.GetBytes(nameSpace),
                name == null ? null : Encoding.UTF8.GetBytes(name),
                paddingMode,
                publicKey,
                privateKey);
        }

        // MakeDefaultCMMWithRSAKeyring is a helper method that creates a default CMM using a RSA Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithRSAKeyring(DafnyFFI.RSAPaddingModes paddingMode)
        {
            Keyring keyring = MakeRSAKeyring(paddingMode, KEYRING_NAMESPACE, KEYRING_NAME);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // MakeAESKeyring is a helper method that creates an AES Keyring for unit testing
        private Keyring MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm, String nameSpace, String name)
        {
            var algorithm = DafnyFFI.AESWrappingAlgorithmToGeneratorUtilitiesAlgorithm(wrappingAlgorithm);
            var keygen = GeneratorUtilities.GetKeyGenerator(algorithm);
            var wrappingKey = keygen.GenerateKey();
            // If namespace or name is null, just pass null into the constructor to properly test this behavior
            return AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                nameSpace == null ? null : Encoding.UTF8.GetBytes(nameSpace),
                name == null ? null : Encoding.UTF8.GetBytes(name),
                wrappingKey,
                wrappingAlgorithm);
        }

        // MakeDefaultCMMWithAESKeyring is a helper method that creates a default CMM using an AES Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithAESKeyring(DafnyFFI.AESWrappingAlgorithm wrappingAlgorithm)
        {
            Keyring keyring = MakeAESKeyring(wrappingAlgorithm, KEYRING_NAMESPACE, KEYRING_NAME);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        // MakeDefaultCMMWithMultiKeyring is a helper method that creates a default CMM using a Multi-Keyring for unit testing
        private CMMDefs.CMM MakeDefaultCMMWithMultiKeyring()
        {
            Keyring generator = MakeKMSKeyring();
            Keyring[] children = new Keyring[] {
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.PKCS1, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA1, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA256, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA384, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA512, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_128, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_192, KEYRING_NAMESPACE, KEYRING_NAME),
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_256, KEYRING_NAMESPACE, KEYRING_NAME),
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
            MemoryStream ciphertext = withParams
                ? AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>(), 0x0346, 2048)
                : AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);
            MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertext, cmm);
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

        [Fact]
        public void BadConstructor_NoKeys_RSA()
        {
            Assert.Throws<ArgumentException>(() => {
                AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
                Encoding.UTF8.GetBytes(KEYRING_NAMESPACE),
                Encoding.UTF8.GetBytes(KEYRING_NAME),
                DafnyFFI.RSAPaddingModes.OAEP_SHA512,
                null,
                null);
            });
        }

        [Fact]
        public void BadConstructor_Namespace_RSA()
        {
            Assert.Throws<ArgumentException>(() => {
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA512, null, KEYRING_NAME);
            });
        }

        [Fact]
        public void BadConstructor_Name_RSA()
        {
            Assert.Throws<ArgumentException>(() => {
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA512, KEYRING_NAMESPACE, null);
            });
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

        [Fact]
        public void BadConstructor_MismatchedWrappingAlgorithm_AES()
        {
            var keygen = GeneratorUtilities.GetKeyGenerator("AES128");
            var wrappingKey = keygen.GenerateKey();
            Assert.Throws<ArgumentException>(() => {
                AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                    Encoding.UTF8.GetBytes("namespace"),
                    Encoding.UTF8.GetBytes("myKeyring"),
                    wrappingKey,
                    DafnyFFI.AESWrappingAlgorithm.AES_GCM_192);
            });
        }

        [Fact]
        public void BadConstructor_Namespace_AES()
        {
            Assert.Throws<ArgumentException>(() => {
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_128, null, KEYRING_NAME);
            });
        }

        [Fact]
        public void BadConstructor_Name_AES()
        {
            Assert.Throws<ArgumentException>(() => {
                MakeAESKeyring(DafnyFFI.AESWrappingAlgorithm.AES_GCM_128, KEYRING_NAMESPACE, null);
            });
        }

        [Fact]
        public void BadConstructor_WrappingKey_AES()
        {
            Assert.Throws<ArgumentException>(() => {
                AWSEncryptionSDK.Keyrings.MakeRawAESKeyring(
                    Encoding.UTF8.GetBytes("namespace"),
                    Encoding.UTF8.GetBytes("myKeyring"),
                    null,
                    DafnyFFI.AESWrappingAlgorithm.AES_GCM_128);
            });
        }

        [Theory]
        [MemberData(nameof(DefaultClientTestData))]
        public void RoundTripHappyPath_MultiKeyring(bool isMultithreaded, bool withParams)
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithMultiKeyring();
            EncryptDecryptThreaded(cmm, isMultithreaded, withParams);
        }

        [Fact]
        public void BadConstructor_NullChild_MultiKeyring()
        {
            Keyring generator = MakeKMSKeyring();
            Keyring[] children = new Keyring[] {
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.PKCS1, KEYRING_NAMESPACE, KEYRING_NAME),
                null,
                MakeRSAKeyring(DafnyFFI.RSAPaddingModes.OAEP_SHA256, KEYRING_NAMESPACE, KEYRING_NAME)
            };
            Assert.Throws<ArgumentException>(() => {
                AWSEncryptionSDK.Keyrings.MakeMultiKeyring(generator, children);
            });
        }

        [Fact]
        public void NullPlaintext()
        {
            var keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
                
            ClientSupplier clientSupplier = new DefaultClientSupplier();
                
            var keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());

            var cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);

            Assert.Throws<NullReferenceException>(() =>
            AWSEncryptionSDK.Client.Encrypt(null, cmm, new Dictionary<string, string>()));
        } 
        
        // TODO-RS: Test for nulls and other Dafny requirement violations
    }
}
