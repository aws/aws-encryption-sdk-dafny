// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public class DecryptMaterialsOutput
    {
        private Aws.Encryption.Core.DecryptionMaterials _decryptionMaterials;

        public Aws.Encryption.Core.DecryptionMaterials DecryptionMaterials
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
            if (!IsSetDecryptionMaterials())
                throw new System.ArgumentException("Missing value for required member 'decryptionMaterials'");
        }
    }
}
