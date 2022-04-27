// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public interface ICryptographicMaterialsManager
    {
        AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput input);

        AWS.EncryptionSDK.Core.DecryptMaterialsOutput DecryptMaterials(
            AWS.EncryptionSDK.Core.DecryptMaterialsInput input);
    }
}
