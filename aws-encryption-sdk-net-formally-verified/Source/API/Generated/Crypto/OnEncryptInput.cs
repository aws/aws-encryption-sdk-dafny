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
    public class OnEncryptInput
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
