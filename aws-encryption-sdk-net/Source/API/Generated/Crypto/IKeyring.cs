// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public interface IKeyring
    {
        AWS.EncryptionSDK.Core.OnEncryptOutput OnEncrypt(AWS.EncryptionSDK.Core.OnEncryptInput input);
        AWS.EncryptionSDK.Core.OnDecryptOutput OnDecrypt(AWS.EncryptionSDK.Core.OnDecryptInput input);
    }
}
