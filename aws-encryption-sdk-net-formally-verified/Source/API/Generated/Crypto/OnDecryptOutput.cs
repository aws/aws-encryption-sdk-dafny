// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class OnDecryptOutput
    {
        private Aws.Crypto.DecryptionMaterials _materials;

        public Aws.Crypto.DecryptionMaterials Materials
        {
            get { return this._materials; }
            set { this._materials = value; }
        }

        public void Validate()
        {
        }
    }
}
