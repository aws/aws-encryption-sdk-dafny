// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Text;

namespace ExampleUtils {
    class ExampleUtils {

        // The name of the environment variable storing the key to use in examples
        private static string TEST_AWS_KMS_KEY_ID_ENV_VAR = "AWS_ENCRYPTION_SDK_EXAMPLE_KMS_KEY_ID";
        static public MemoryStream GetPlaintextStream() {
            return new MemoryStream(Encoding.UTF8.GetBytes(
                        "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
                        ));
        }

        static public string GetKmsKeyArn() {
            string keyId = System.Environment.GetEnvironmentVariable(TEST_AWS_KMS_KEY_ID_ENV_VAR);
            if (keyId == null) {
                throw new ArgumentException(
                    String.Format("Please set environment variable {0} to a valid KMS key id", TEST_AWS_KMS_KEY_ID_ENV_VAR)
                );
            }
            return keyId;
        }
    }
}
