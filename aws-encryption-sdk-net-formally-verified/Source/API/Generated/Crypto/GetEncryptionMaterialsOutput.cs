// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEncryptionMaterialsOutput
    {
        private Aws.Crypto.EncryptionMaterials _encryptionMaterials;

        public Aws.Crypto.EncryptionMaterials EncryptionMaterials
        {
            get { return this._encryptionMaterials; }
            set { this._encryptionMaterials = value; }
        }

        internal bool IsSetEncryptionMaterials()
        {
            return this._encryptionMaterials != null;
        }

        public void Validate()
        {
            if (!IsSetEncryptionMaterials())
                throw new System.ArgumentException("Missing value for required member 'encryptionMaterials'");
        }
    }
}
