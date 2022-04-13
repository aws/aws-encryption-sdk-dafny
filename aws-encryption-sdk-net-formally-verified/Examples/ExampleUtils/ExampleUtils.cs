// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Amazon;
using AWS.EncryptionSDK.Core;
using Org.BouncyCastle.Security;

namespace ExampleUtils {
    class ExampleUtils {

        // The name of the environment variable storing the key to use in examples
        private static string TEST_AWS_KMS_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID";
        private static string TEST_AWS_KMS_KEY_ID_2_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID_2";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR_2 = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID_2";

        /// Returns the number of Keys used by the examples.
        /// Bare in mind:
        /// - MRK replica's should not be double counted
        /// - Raw AES and RSA Keys count
        public static int GetMaxExampleKeys()
        {
            return 5;
        }

        static public MemoryStream GetPlaintextStream() {
            return new MemoryStream(Encoding.UTF8.GetBytes(
                        "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
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

        // Helper method to create RawAESKeyring for examples.
        public static IKeyring GetRawAESKeyring(IAwsCryptographicMaterialProviders materialProviders)
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
    }
}
