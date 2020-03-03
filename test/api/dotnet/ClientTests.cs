using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using KeyringDefs;
using KMSUtils;
using Xunit;

namespace AWSEncryptionSDKTests
{
    public class ClientTests
    {

        private CMMDefs.CMM MakeDefaultCMMWithKMSKeyring()
        {
            String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
            ClientSupplier clientSupplier = new DefaultClientSupplier();
            Keyring keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        private String DecodeMemoryStream(MemoryStream ciphertext, CMMDefs.CMM cmm)
        {
            MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertext, cmm);
            StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
            return reader.ReadToEnd();
        }

        [Fact]
        public void RoundTripHappyPath()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("Hello"));

            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);

            String decoded = DecodeMemoryStream(ciphertext, cmm);
            Assert.Equal("Hello", decoded);
        }

        [Fact]
        public void RoundTripHappyPathWithParams()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes("Hello"));

            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>(), 0x0346, 2048);

            String decoded = DecodeMemoryStream(ciphertext, cmm);
            Assert.Equal("Hello", decoded);
        }

        private void EncryptDecryptThread(CMMDefs.CMM cmm, int threadNum, Dictionary<int, string> results, String plainText)
        {
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plainText));
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);
            String decoded = DecodeMemoryStream(ciphertext, cmm);
            lock (results) {
                results.Add(threadNum, decoded);
            }
        }

        private void TestEncryptDecryptMultiThreaded(CMMDefs.CMM cmm)
        {
            var totalThreads = 100;
            var threadTimeout = TimeSpan.FromSeconds(30);
            var plainTextTemplate = "Hello from thread {0}";

            var threads = new List<Thread>();
            var results = new Dictionary<int, string>();

            // Create threads, run them, and ensure we don't terminate until all threads terminate (or timeout occurs)
            for (int x = 0; x < totalThreads; x++) {
                // x is not used directly in EncryptDecryptThread because this would cause x = totalThreads for all theads
                var threadNum = x;
                var plaintext = String.Format(plainTextTemplate, threadNum);
                threads.Add(new Thread(() => EncryptDecryptThread(cmm, threadNum, results, plaintext))); 
            }
            foreach (var thread in threads) { thread.Start(); }
            foreach (var thread in threads) { thread.Join(threadTimeout); }

            // Verify all responses
            for (int x = 0; x < totalThreads; x++) {
                Assert.True(results.ContainsKey(x));
                var expected = String.Format(plainTextTemplate, x);
                Assert.Equal(expected, results[x]);
            }
        }

        [Fact]
        public void RoundTripHappyPathThreadedDefaultCMMWithKMS()
        {
            CMMDefs.CMM cmm = MakeDefaultCMMWithKMSKeyring();
            TestEncryptDecryptMultiThreaded(cmm);
        }
    }
}
