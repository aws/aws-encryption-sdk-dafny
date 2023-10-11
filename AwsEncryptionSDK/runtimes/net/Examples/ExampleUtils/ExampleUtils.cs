// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Text;
using Amazon;
using Amazon.KeyManagementService;
using Amazon.KeyManagementService.Model;
using AWS.Cryptography.EncryptionSDK;
using AWS.Cryptography.MaterialProviders;
using Org.BouncyCastle.Security;
using AesWrappingAlg = AWS.Cryptography.MaterialProviders.AesWrappingAlg;
using CreateAwsKmsMrkMultiKeyringInput = AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkMultiKeyringInput;
using CreateRawAesKeyringInput = AWS.Cryptography.MaterialProviders.CreateRawAesKeyringInput;
using IKeyring = AWS.Cryptography.MaterialProviders.IKeyring;

namespace ExampleUtils {
    class ExampleUtils {

        // The name of the environment variable storing the key to use in examples
        private static string TEST_AWS_KMS_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID";
        private static string TEST_AWS_KMS_KEY_ID_2_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID_2";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR_2 = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID_2";

        // The name of the environment variable storing the IAM Role Arn to use in examples
        private static string TEST_AWS_LIMITED_ROLE_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_LIMITED_ROLE_ARN_US_EAST_1";
        private static string TEST_AWS_LIMITED_ROLE_ENV_VAR_2 = "AWS_ENCRYPTION_SDK_EXAMPLE_LIMITED_ROLE_ARN_EU_WEST_1";
        // THESE ARE PUBLIC RESOURCES. DO NOT USE IN A PRODUCTION ENVIRONMENT.
        private static string BRANCH_KEY_STORE_NAME = "KeyStoreDdbTable";
        private static string LOGICAL_KEY_STORE_NAME = BRANCH_KEY_STORE_NAME;
        private static string BRANCH_KEY_ARN = "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";

        private const string ENCRYPTED_MESSAGE_PATH = "../../../resources/";

        private static readonly ImmutableDictionary<string, string> ENCRYPTION_CONTEXT = new Dictionary<string, string>
        {
            {"encryption", "context"},
            {"is not", "secret"},
            {"but adds", "useful metadata"},
            {"that can help you", "be confident that"},
            {"the data you are handling", "is what you think it is"}
        }.ToImmutableDictionary();

        static public MemoryStream GetPlaintextStream() {
            return new MemoryStream(Encoding.UTF8.GetBytes(
                        "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
                        ));
        }

        static public MemoryStream GetKmsRSAPublicKey()
        {
            // THIS IS A PUBLIC RESOURCE AND SHOULD NOT BE USED IN A PRODUCTION ENVIRONMENT
            return new MemoryStream(Encoding.UTF8.GetBytes(
                "-----BEGIN PUBLIC KEY-----"+ 
                "MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA27Uc/fBaMVhxCE/SpCMQ"+ 
                "oSBRSzQJw+o2hBaA+FiPGtiJ/aPy7sn18aCkelaSj4kwoC79b/arNHlkjc7OJFsN"+
                "/GoFKgNvaiY4lOeJqEiWQGSSgHtsJLdbO2u4OOSxh8qIRAMKbMgQDVX4FR/PLKeK"+ 
                "fc2aCDvcNSpAM++8NlNmv7+xQBJydr5ce91eISbHkFRkK3/bAM+1iddupoRw4Wo2"+
                "r3avzrg5xBHmzR7u1FTab22Op3Hgb2dBLZH43wNKAceVwKqKA8UNAxashFON7xK9" + 
                "yy4kfOL0Z/nhxRKe4jRZ/5v508qIzgzCksYy7Y3QbMejAtiYnr7s5/d5KWw0swou"+ 
                "twIDAQAB"+
                "-----END PUBLIC KEY-----"
                ));
        }

        static public string GetEnvVariable(string keyName)
        {
            string value = Environment.GetEnvironmentVariable(keyName);
            if (value == null) {
                throw new ArgumentException(
                    String.Format("Please set environment variable {0} to a valid KMS key ARN", keyName)
                );
            }
            return value;
        }

        static public RegionEndpoint GetRegionEndpointFromArn(string arn_string)
        {
            Arn arn = Arn.Parse(arn_string);
            return RegionEndpoint.GetBySystemName(arn.Region);
        }

        static public string GetDefaultRegionKmsKeyArn()
        {
            return GetEnvVariable(TEST_AWS_KMS_KEY_ID_ENV_VAR);
        }

        static public string GetAlternateRegionKmsKeyArn()
        {
            return GetEnvVariable(TEST_AWS_KMS_KEY_ID_2_ENV_VAR);
        }

        static public string GetDefaultRegionMrkKeyArn()
        {
            return GetEnvVariable(TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR);
        }

        static public string GetAlternateRegionMrkKeyArn()
        {
            return GetEnvVariable(TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR_2);
        }

        static public List<string> GetAccountIds()
        {
            return new List<string>() {"658956600833"};
        }

        static public List<string> GetRegions()
        {
            return new List<string>() {"us-west-2", "us-east-1"};
        }

        static public Dictionary<string, string> GetRegionIAMRoleMap()
        {
            return new Dictionary<string, string>()
            {
                {RegionEndpoint.USEast1.SystemName, GetEnvVariable(TEST_AWS_LIMITED_ROLE_ENV_VAR)},
                {RegionEndpoint.EUWest1.SystemName, GetEnvVariable(TEST_AWS_LIMITED_ROLE_ENV_VAR_2)}
            };
        }

        static public string GetBranchKeyArn()
        {
            return BRANCH_KEY_ARN;
        }

        static public string GetKeyStoreName()
        {
            return BRANCH_KEY_STORE_NAME;
        }

        static public string GetLogicalKeyStoreName()
        {
            return LOGICAL_KEY_STORE_NAME;
        }
        

        // Helper method to create RawAESKeyring for examples.
        public static IKeyring GetRawAESKeyring(MaterialProviders materialProviders)
        {
            // Generate a 256-bit AES key to use with your keyring.
            // Here we use BouncyCastle, but you don't have to.
            //
            // In practice, you should get this key from a secure key management system such as an HSM.
            var key = new MemoryStream(GeneratorUtilities.GetKeyGenerator("AES256").GenerateKey());

            // The key namespace and key name are defined by you
            // and are used by the raw AES keyring to determine
            // whether it should attempt to decrypt an encrypted data key.
            //
            // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/choose-keyring.html#use-raw-aes-keyring
            var keyNamespace = "Some managed raw keys";
            var keyName = "My 256-bit AES wrapping key";

            // Create the keyring that determines how your data keys are protected.
            var createAesKeyringInput = new CreateRawAesKeyringInput
            {
                KeyNamespace = keyNamespace,
                KeyName = keyName,
                WrappingKey = key,
                WrappingAlg = AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16
            };
            var aesKeyring = materialProviders.CreateRawAesKeyring(createAesKeyringInput);

            return aesKeyring;
        }

        public static ICryptographicMaterialsManager GetRequiredEncryptionContextCMM(
            MaterialProviders materialProviders, List<string> requiredEncryptionContextKeys, IKeyring keyring
        )
        {
            // Create a Required Encryption Context CMM
            var requiredEncryptionContextCMMInput = new CreateRequiredEncryptionContextCMMInput
            {
                
                UnderlyingCMM = materialProviders.CreateDefaultCryptographicMaterialsManager(
                    new CreateDefaultCryptographicMaterialsManagerInput{Keyring = keyring}),
                // If you pass in a keyring but no underlying cmm, it will result in a failure because only cmm is supported.
                RequiredEncryptionContextKeys = requiredEncryptionContextKeys 
            };

            var requiredEncryptionContextCMM =
                materialProviders.CreateRequiredEncryptionContextCMM(requiredEncryptionContextCMMInput);
            
            return requiredEncryptionContextCMM;
        }

        public static Dictionary<string, string> GetEncryptionContext()
        {
            return ENCRYPTION_CONTEXT.ToDictionary(p => p.Key, p => p.Value);
        }

        public static MemoryStream EncryptMessageWithKMSKey(MemoryStream plaintext, string kmsKeyArn)
        {
            var materialProviders = new MaterialProviders(new MaterialProvidersConfig());
            var encryptionSdk = new ESDK(new AwsEncryptionSdkConfig());
            var createKeyringInput = new CreateAwsKmsMrkMultiKeyringInput()
            {
                Generator = kmsKeyArn
            };
            var encryptKeyring = materialProviders.CreateAwsKmsMrkMultiKeyring(createKeyringInput);
            var encryptInput = new EncryptInput
            {
                Plaintext = plaintext,
                Keyring = encryptKeyring,
                EncryptionContext = GetEncryptionContext()
            };
            var encryptOutput = encryptionSdk.Encrypt(encryptInput);
            var ciphertext = encryptOutput.Ciphertext;
            return ciphertext;
        }

        public static string GetResourcePath(string name)
        {
            return ENCRYPTED_MESSAGE_PATH + name;
        }

        public static void WriteMessage(MemoryStream message, string path)
        {
            using (var file = new FileStream(GetResourcePath(path), FileMode.OpenOrCreate, FileAccess.Write))
                message.CopyTo(file);
        }

        public static MemoryStream ReadMessage(string path)
        {
            var rtn = new MemoryStream();
            using (var file = new FileStream(GetResourcePath(path), FileMode.Open, FileAccess.Read))
                file.CopyTo(rtn);
            return rtn;
        }
    }
}
