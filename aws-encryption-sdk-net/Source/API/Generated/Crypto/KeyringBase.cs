// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public abstract class KeyringBase : IKeyring
    {
        public AWS.EncryptionSDK.Core.OnEncryptOutput OnEncrypt(AWS.EncryptionSDK.Core.OnEncryptInput input)
        {
            input.Validate();
            return _OnEncrypt(input);
        }

        protected abstract AWS.EncryptionSDK.Core.OnEncryptOutput _OnEncrypt(
            AWS.EncryptionSDK.Core.OnEncryptInput input);

        public AWS.EncryptionSDK.Core.OnDecryptOutput OnDecrypt(AWS.EncryptionSDK.Core.OnDecryptInput input)
        {
            input.Validate();
            return _OnDecrypt(input);
        }

        protected abstract AWS.EncryptionSDK.Core.OnDecryptOutput _OnDecrypt(
            AWS.EncryptionSDK.Core.OnDecryptInput input);
    }
}
