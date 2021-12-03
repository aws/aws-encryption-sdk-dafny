// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:30:30.159384

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager
    {
        public Aws.Crypto.GetEncryptionMaterialsOutput GetEncryptionMaterials(
            Aws.Crypto.GetEncryptionMaterialsInput input)
        {
            input.Validate();
            return _GetEncryptionMaterials(input);
        }

        protected abstract Aws.Crypto.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            Aws.Crypto.GetEncryptionMaterialsInput input);

        public Aws.Crypto.DecryptMaterialsOutput DecryptMaterials(Aws.Crypto.DecryptMaterialsInput input)
        {
            input.Validate();
            return _DecryptMaterials(input);
        }

        protected abstract Aws.Crypto.DecryptMaterialsOutput _DecryptMaterials(Aws.Crypto.DecryptMaterialsInput input);
    }
}
