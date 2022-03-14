// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public interface ICryptographicMaterialsManager
    {
        Aws.Encryption.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            Aws.Encryption.Core.GetEncryptionMaterialsInput input);

        Aws.Encryption.Core.DecryptMaterialsOutput DecryptMaterials(Aws.Encryption.Core.DecryptMaterialsInput input);
    }
}
