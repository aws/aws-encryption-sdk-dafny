using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using KeyringDefs;
using KMSUtils;
using Xunit;

using charseq = Dafny.Sequence<char>;


namespace AWSEncryptionSDKTests
{
    public class ClientTests
    {
        
        
        [Fact]
        public void RoundTripHappyPath()
        {
            String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);

            ClientSupplier clientSupplier = new DefaultClientSupplier();

            var keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());

            CMMDefs.CMM cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);

            String plaintext = "Hello";
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));

            MemoryStream ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm);

            MemoryStream decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertext, cmm);
            StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
            String decoded = reader.ReadToEnd();

            Assert.Equal(plaintext, decoded);
        }

        [Fact]
        public void RoundTripHappyPathWithParams()
        {
            String keyArn = DafnyFFI.StringFromDafnyString(TestUtils.__default.SHARED__TEST__KEY__ARN);

            ClientSupplier clientSupplier = new DefaultClientSupplier();

            var keyring = AWSEncryptionSDK.Keyrings.MakeKMSKeyring(
                clientSupplier, Enumerable.Empty<String>(), keyArn,Enumerable.Empty<String>());

            var cmm = AWSEncryptionSDK.CMMs.MakeDefaultCMM(keyring);

            var plaintext = "Hello";
            var plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
            
            var ciphertext = AWSEncryptionSDK.Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>());
            
            var decodedStream = AWSEncryptionSDK.Client.Decrypt(ciphertext, cmm);
            var reader = new StreamReader(decodedStream, Encoding.UTF8);
            var decoded = reader.ReadToEnd();
            
            Assert.Equal(plaintext, decoded);
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
        
        [Fact]
        public void NullKeyring()
        {
            Assert.Throws<NullReferenceException>(() => AWSEncryptionSDK.CMMs.MakeDefaultCMM(null));
        } 
    }
}
