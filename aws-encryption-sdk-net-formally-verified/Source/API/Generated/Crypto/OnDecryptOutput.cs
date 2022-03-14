// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public class OnDecryptOutput
    {
        private Aws.Encryption.Core.DecryptionMaterials _materials;

        public Aws.Encryption.Core.DecryptionMaterials Materials
        {
            get { return this._materials; }
            set { this._materials = value; }
        }

        internal bool IsSetMaterials()
        {
            return this._materials != null;
        }

        public void Validate()
        {
            if (!IsSetMaterials()) throw new System.ArgumentException("Missing value for required member 'materials'");
        }
    }
}
