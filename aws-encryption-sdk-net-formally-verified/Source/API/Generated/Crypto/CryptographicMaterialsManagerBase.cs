// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager
    {
        public Aws.Encryption.Core.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            Aws.Encryption.Core.GetEncryptionMaterialsInput input)
        {
            input.Validate();
            return _GetEncryptionMaterials(input);
        }

        protected abstract Aws.Encryption.Core.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            Aws.Encryption.Core.GetEncryptionMaterialsInput input);

        public Aws.Encryption.Core.DecryptMaterialsOutput DecryptMaterials(
            Aws.Encryption.Core.DecryptMaterialsInput input)
        {
            input.Validate();
            return _DecryptMaterials(input);
        }

        protected abstract Aws.Encryption.Core.DecryptMaterialsOutput _DecryptMaterials(
            Aws.Encryption.Core.DecryptMaterialsInput input);
    }
}
