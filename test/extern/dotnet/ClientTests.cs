using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using ESDK;
using KMSKeyringDefs;
using KMSUtils;
using STL;
using Xunit;

using charseq = Dafny.Sequence<char>;


namespace AWSEncryptionSDKTests
{
    public class ClientTests
    {
        [Fact]
        public void HappyPath()
        {
            String keyArn = "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
            charseq keyArnDafny = DafnyFFI.DafnyStringFromString(keyArn);
            ClientSupplier clientSupplier = new DefaultClientSupplier();
            
            KMSKeyring keyring = KMSKeyringDefs.__default.MakeKMSKeyring(clientSupplier, Dafny.Sequence<charseq>.Empty,
                    new Option_Some<charseq>(keyArnDafny),
                    Dafny.Sequence<charseq>.Empty);
            
            DefaultCMM cmm = new DefaultCMM();
            cmm.OfKeyring(keyring);

            String plaintext = "Hello";
            MemoryStream plaintextStream = new MemoryStream(Encoding.UTF8.GetBytes(plaintext));
            
            MemoryStream ciphertext = Client.Encrypt(plaintextStream, cmm, new Dictionary<string, string>());
            
            MemoryStream decodedStream = Client.Decrypt(ciphertext, cmm);
            StreamReader reader = new StreamReader(decodedStream, Encoding.UTF8);
            String decoded = reader.ReadToEnd();
            
            Assert.Equal(plaintext, decoded);
        } 
    }
}