// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public class DecryptMaterialsOutput
    {
        private AWS.EncryptionSDK.Core.DecryptionMaterials _decryptionMaterials;

        public AWS.EncryptionSDK.Core.DecryptionMaterials DecryptionMaterials
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
                throw new System.ArgumentException("Missing value for required property 'DecryptionMaterials'");
        }
    }
}
