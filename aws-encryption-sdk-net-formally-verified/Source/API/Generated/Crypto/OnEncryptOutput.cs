// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class OnEncryptOutput
    {
        private Aws.Crypto.EncryptionMaterials _materials;

        public Aws.Crypto.EncryptionMaterials Materials
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
