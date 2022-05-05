// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    public interface IAwsEncryptionSdk
    {
        AWS.EncryptionSDK.EncryptOutput Encrypt(AWS.EncryptionSDK.EncryptInput input);
        AWS.EncryptionSDK.DecryptOutput Decrypt(AWS.EncryptionSDK.DecryptInput input);
    }
}
