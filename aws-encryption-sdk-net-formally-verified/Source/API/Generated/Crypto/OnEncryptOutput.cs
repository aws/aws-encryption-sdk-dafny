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

        public void Validate()
        {
        }
    }
}
