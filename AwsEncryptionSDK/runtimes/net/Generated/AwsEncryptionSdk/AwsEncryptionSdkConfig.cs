// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.EncryptionSDK;
namespace AWS.Cryptography.EncryptionSDK
{
    public class AwsEncryptionSdkConfig
    {
        private AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy _commitmentPolicy;
        private long? _maxEncryptedDataKeys;
        private AWS.Cryptography.EncryptionSDK.NetV4_0_0_RetryPolicy _netV4_0_0_RetryPolicy;
        public AWS.Cryptography.MaterialProviders.ESDKCommitmentPolicy CommitmentPolicy
        {
            get { return this._commitmentPolicy; }
            set { this._commitmentPolicy = value; }
        }
        public bool IsSetCommitmentPolicy()
        {
            return this._commitmentPolicy != null;
        }
        public long MaxEncryptedDataKeys
        {
            get { return this._maxEncryptedDataKeys.GetValueOrDefault(); }
            set { this._maxEncryptedDataKeys = value; }
        }
        public bool IsSetMaxEncryptedDataKeys()
        {
            return this._maxEncryptedDataKeys.HasValue;
        }
        public AWS.Cryptography.EncryptionSDK.NetV4_0_0_RetryPolicy NetV4__0__0__RetryPolicy
        {
            get { return this._netV4_0_0_RetryPolicy; }
            set { this._netV4_0_0_RetryPolicy = value; }
        }
        public bool IsSetNetV4__0__0__RetryPolicy()
        {
            return this._netV4_0_0_RetryPolicy != null;
        }
        public void Validate()
        {

        }
    }
}
