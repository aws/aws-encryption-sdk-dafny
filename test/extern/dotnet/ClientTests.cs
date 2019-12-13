using System;
using _65_KMSKeyring_Compile;
using Amazon.KeyManagementService;
using Dafny;
using KMSUtils;
using STL;
using Xunit;

namespace AWSEncryptionSDKTests
{
    
    public class ClientTests
    {
        [Fact]
        public void HappyPath()
        {
            String keyArn = "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";
            ClientSupplier clientSupplier = new DefaultClientSupplier();
            KMSKeyring keyring = new KMSKeyring();
        } 
    }
}