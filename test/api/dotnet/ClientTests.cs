using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks.Dataflow;
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

        private string EncryptDecryptThread(CMMDefs.CMM cmm, int id)
        {
            var plaintext = String.Format("Hello from id {0}", id);
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);
            String decoded = DecodeMemoryStream(ciphertext, cmm);
            return (plaintext == decoded) ? decoded : String.Format("Id: {0} failed, decoded: {1}", id, decoded);
        }

        private void TestEncryptDecryptMultiThreaded(CMMDefs.CMM cmm)
        {
            var maxDegreeOfParallelism = Environment.ProcessorCount * 4;
            var transformBlock = new TransformBlock<int, string>(
                id => EncryptDecryptThread(cmm, id),
                new ExecutionDataflowBlockOptions { MaxDegreeOfParallelism = maxDegreeOfParallelism }
            );

            for (int i = 0; i < maxDegreeOfParallelism; i++) {
                transformBlock.Post(i);
            }

            for (int i = 0; i < maxDegreeOfParallelism; i++) {
                Assert.StartsWith("Hello", transformBlock.Receive());
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
