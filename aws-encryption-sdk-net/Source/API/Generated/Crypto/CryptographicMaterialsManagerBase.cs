// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager
    {
        public AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput input)
        {
            input.Validate();
            return _GetEncryptionMaterials(input);
        }

        protected abstract AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput input);

        public AWS.EncryptionSDK.Core.DecryptMaterialsOutput DecryptMaterials(
            AWS.EncryptionSDK.Core.DecryptMaterialsInput input)
        {
            input.Validate();
            return _DecryptMaterials(input);
        }

        protected abstract AWS.EncryptionSDK.Core.DecryptMaterialsOutput _DecryptMaterials(
            AWS.EncryptionSDK.Core.DecryptMaterialsInput input);
    }
}
