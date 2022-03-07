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
        private long? _maxEncryptedDataKeys;
        private Aws.Esdk.ConfigurationDefaults _configDefaults;

        public Aws.Crypto.CommitmentPolicy CommitmentPolicy
        {
            get { return this._commitmentPolicy; }
            set { this._commitmentPolicy = value; }
        }

        internal bool IsSetCommitmentPolicy()
        {
            return this._commitmentPolicy != null;
        }

        public long MaxEncryptedDataKeys
        {
            get { return this._maxEncryptedDataKeys.GetValueOrDefault(); }
            set { this._maxEncryptedDataKeys = value; }
        }

        internal bool IsSetMaxEncryptedDataKeys()
        {
            return this._maxEncryptedDataKeys.HasValue;
        }

        public Aws.Esdk.ConfigurationDefaults ConfigDefaults
        {
            get { return this._configDefaults; }
            set { this._configDefaults = value; }
        }

        internal bool IsSetConfigDefaults()
        {
            return this._configDefaults != null;
        }

        public void Validate()
        {
        }
    }
}
