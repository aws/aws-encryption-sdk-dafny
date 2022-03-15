// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public class OnDecryptInput
    {
        private Aws.EncryptionSdk.Core.DecryptionMaterials _materials;
        private System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> _encryptedDataKeys;

        public Aws.EncryptionSdk.Core.DecryptionMaterials Materials
        {
            get { return this._materials; }
            set { this._materials = value; }
        }

        internal bool IsSetMaterials()
        {
            return this._materials != null;
        }

        public System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> EncryptedDataKeys
        {
            get { return this._encryptedDataKeys; }
            set { this._encryptedDataKeys = value; }
        }

        internal bool IsSetEncryptedDataKeys()
        {
            return this._encryptedDataKeys != null;
        }

        public void Validate()
        {
            if (!IsSetMaterials()) throw new System.ArgumentException("Missing value for required member 'materials'");
            if (!IsSetEncryptedDataKeys())
                throw new System.ArgumentException("Missing value for required member 'encryptedDataKeys'");
        }
    }
}
