// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager
    {
        public Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput input)
        {
            input.Validate();
            return _GetEncryptionMaterials(input);
        }

        protected abstract Aws.EncryptionSdk.Core.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            Aws.EncryptionSdk.Core.GetEncryptionMaterialsInput input);

        public Aws.EncryptionSdk.Core.DecryptMaterialsOutput DecryptMaterials(
            Aws.EncryptionSdk.Core.DecryptMaterialsInput input)
        {
            input.Validate();
            return _DecryptMaterials(input);
        }

        protected abstract Aws.EncryptionSdk.Core.DecryptMaterialsOutput _DecryptMaterials(
            Aws.EncryptionSdk.Core.DecryptMaterialsInput input);
    }
}
