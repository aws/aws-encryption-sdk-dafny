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
    using Amazon.Runtime;

    public class ConfigurationDefaults : ConstantClass
    {
        public static readonly ConfigurationDefaults V1 = new ConfigurationDefaults("V1");

        public static readonly ConfigurationDefaults[] Values =
        {
            V1
        };

        public ConfigurationDefaults(string value) : base(value)
        {
        }
    }
}