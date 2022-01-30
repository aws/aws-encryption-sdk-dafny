// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class AwsEncryptionSdkClientConfig
    {
        private Aws.Crypto.CommitmentPolicy _commitmentPolicy;
        private Aws.Esdk.ConfigurationDefaults _configDefaults;

        public Aws.Crypto.CommitmentPolicy CommitmentPolicy
        {
            get { return this._commitmentPolicy; }
            set { this._commitmentPolicy = value; }
        }

        public Aws.Esdk.ConfigurationDefaults ConfigDefaults
        {
            get { return this._configDefaults; }
            set { this._configDefaults = value; }
        }

        public void Validate()
        {
        }
    }
}
