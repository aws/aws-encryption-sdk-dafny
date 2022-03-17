// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public interface ICryptographicMaterialsManager
    {
        Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput input);

        Aws.EncryptionSdk.Core.DecryptMaterialsOutput DecryptMaterials(
            Aws.EncryptionSdk.Core.DecryptMaterialsInput input);
    }
}
