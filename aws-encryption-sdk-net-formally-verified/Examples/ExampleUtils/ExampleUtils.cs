// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Amazon;

namespace ExampleUtils {
    class ExampleUtils {

        // The name of the environment variable storing the key to use in examples
        private static string TEST_AWS_KMS_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID";
        private static string TEST_AWS_KMS_KEY_ID_2_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID_2";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID";
        private static string TEST_AWS_KMS_MRK_KEY_ID_ENV_VAR_2 = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_MRK_KEY_ID_2";

        static public MemoryStream GetPlaintextStream() {
            return new MemoryStream(Encoding.UTF8.GetBytes(
                        "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
                        ));
        }

        static public string GetEnvVariable(string keyName)
        {
            string value = System.Environment.GetEnvironmentVariable(keyName);
            if (value == null) {
                throw new ArgumentException(
                    String.Format("Please set environment variable {0} to a valid KMS key ARN", keyName)
                );
            }
            return value;
        }

        static public string GetRegionStringFromArn(string arn_string)
        {
            Arn arn = Arn.Parse(arn_string);
            return arn.Region;
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
    }
}
