// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:32:59.305823

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class AwsEncryptionSdkClientConfig
    {
        public ConfigurationDefaults ConfigDefaults { get; private set; }

        public static IAwsEncryptionSdkClientConfigBuilder Builder()
        {
            return new AwsEncryptionSdkClientConfigBuilder();
        }

        public void Validate()
        {
        }

        private class AwsEncryptionSdkClientConfigBuilder : IAwsEncryptionSdkClientConfigBuilder
        {
            private ConfigurationDefaults ConfigDefaults;

            public IAwsEncryptionSdkClientConfigBuilder WithConfigDefaults(ConfigurationDefaults value)
            {
                ConfigDefaults = value;
                return this;
            }

            public AwsEncryptionSdkClientConfig Build()
            {
                if (ConfigDefaults == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "configDefaults"));
                }

                return new AwsEncryptionSdkClientConfig
                {
                    ConfigDefaults = (ConfigurationDefaults) ConfigDefaults,
                };
            }
        }
    }

    public interface IAwsEncryptionSdkClientConfigBuilder
    {
        IAwsEncryptionSdkClientConfigBuilder WithConfigDefaults(ConfigurationDefaults value);
        AwsEncryptionSdkClientConfig Build();
    }
}