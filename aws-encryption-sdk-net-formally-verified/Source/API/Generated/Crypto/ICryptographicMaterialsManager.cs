// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public interface ICryptographicMaterialsManager
    {
        Aws.Crypto.GetEncryptionMaterialsOutput GetEncryptionMaterials(Aws.Crypto.GetEncryptionMaterialsInput input);
        Aws.Crypto.DecryptMaterialsOutput DecryptMaterials(Aws.Crypto.DecryptMaterialsInput input);
    }
}
