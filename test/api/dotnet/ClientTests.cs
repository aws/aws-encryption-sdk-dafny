using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using KeyringDefs;
using KMSUtils;
using Xunit;

namespace AWSEncryptionSDKTests
{
    public class ClientTests
    {

        private static string SUCCESS = "SUCCESS";

        private CMMDefs.CMM MakeDefaultCMMWithKMSKeyring()
        {
            String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);
            ClientSupplier clientSupplier = new DefaultClientSupplier();
            Keyring keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

        private CMMDefs.CMM MakeDefaultCMMWithRSAKeyring(DafnyFFI.RSAPaddingModes paddingMode)
        {
            ClientSupplier clientSupplier = new DefaultClientSupplier();
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
            Keyring keyring = AWSEncryptionSDK.Keyrings.MakeRawRSAKeyring(
                Encoding.UTF8.GetBytes("namespace"),
                Encoding.UTF8.GetBytes("myKeyring"),
                paddingMode,
                publicKey,
                privateKey);
            return AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);
        }

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
            var totalIds = Environment.ProcessorCount * 4;
            var concurrentBag = new ConcurrentBag<String>();
            Parallel.For(
                0, totalIds,
                id => { concurrentBag.Add(EncryptDecrypt(cmm, id, withParams)); }
            );
            var totalDecoded = 0;
            foreach (string decoded in concurrentBag) {
                Assert.Equal(SUCCESS, decoded);
                totalDecoded += 1;
            }
            // Sanity check the total number of ids processed
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
    }
}
