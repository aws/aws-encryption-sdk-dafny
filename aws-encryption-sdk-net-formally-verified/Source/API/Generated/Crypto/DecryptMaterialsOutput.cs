// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DecryptMaterialsOutput
    {
        private Aws.Crypto.DecryptionMaterials _decryptionMaterials;

        public Aws.Crypto.DecryptionMaterials DecryptionMaterials
        {
            get { return this._decryptionMaterials; }
            set { this._decryptionMaterials = value; }
        }

        internal bool IsSetDecryptionMaterials()
        {
            return this._decryptionMaterials != null;
        }

        public void Validate()
        {
        }
    }
}
