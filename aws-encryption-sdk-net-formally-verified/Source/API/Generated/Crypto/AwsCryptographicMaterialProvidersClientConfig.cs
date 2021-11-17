// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class AwsCryptographicMaterialProvidersClientConfig
    {
        public ConfigurationDefaults ConfigDefaults { get; private set; }

        public static IAwsCryptographicMaterialProvidersClientConfigBuilder Builder()
        {
            return new AwsCryptographicMaterialProvidersClientConfigBuilder();
        }

        public void Validate()
        {
        }

        private class
            AwsCryptographicMaterialProvidersClientConfigBuilder : IAwsCryptographicMaterialProvidersClientConfigBuilder
        {
            private ConfigurationDefaults ConfigDefaults;

            public IAwsCryptographicMaterialProvidersClientConfigBuilder WithConfigDefaults(ConfigurationDefaults value)
            {
                ConfigDefaults = value;
                return this;
            }

            public AwsCryptographicMaterialProvidersClientConfig Build()
            {
                if (ConfigDefaults == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "configDefaults"));
                }

                return new AwsCryptographicMaterialProvidersClientConfig
                {
                    ConfigDefaults = (ConfigurationDefaults) ConfigDefaults,
                };
            }
        }
    }

    public interface IAwsCryptographicMaterialProvidersClientConfigBuilder
    {
        IAwsCryptographicMaterialProvidersClientConfigBuilder WithConfigDefaults(ConfigurationDefaults value);
        AwsCryptographicMaterialProvidersClientConfig Build();
    }
}