// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:21:59.652135

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class CryptographicMaterialsManagerBase : ICryptographicMaterialsManager
    {
        public GetEncryptionMaterialsOutput GetEncryptionMaterials(GetEncryptionMaterialsInput input)
        {
            input.Validate();
            return _GetEncryptionMaterials(input);
        }

        protected abstract GetEncryptionMaterialsOutput _GetEncryptionMaterials(GetEncryptionMaterialsInput input);

        public DecryptMaterialsOutput DecryptMaterials(DecryptMaterialsInput input)
        {
            input.Validate();
            return _DecryptMaterials(input);
        }

        protected abstract DecryptMaterialsOutput _DecryptMaterials(DecryptMaterialsInput input);
    }
}
