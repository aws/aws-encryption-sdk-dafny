// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    public abstract class AwsEncryptionSdkBase : IAwsEncryptionSdk
    {
        public AWS.EncryptionSDK.EncryptOutput Encrypt(AWS.EncryptionSDK.EncryptInput input)
        {
            input.Validate();
            return _Encrypt(input);
        }

        protected abstract AWS.EncryptionSDK.EncryptOutput _Encrypt(AWS.EncryptionSDK.EncryptInput input);

        public AWS.EncryptionSDK.DecryptOutput Decrypt(AWS.EncryptionSDK.DecryptInput input)
        {
            input.Validate();
            return _Decrypt(input);
        }

        protected abstract AWS.EncryptionSDK.DecryptOutput _Decrypt(AWS.EncryptionSDK.DecryptInput input);
    }
}
