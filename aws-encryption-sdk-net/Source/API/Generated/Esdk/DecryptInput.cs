// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    public class DecryptInput
    {
        private System.IO.MemoryStream _ciphertext;
        private AWS.EncryptionSDK.Core.ICryptographicMaterialsManager _materialsManager;
        private AWS.EncryptionSDK.Core.IKeyring _keyring;

        public System.IO.MemoryStream Ciphertext
        {
            get { return this._ciphertext; }
            set { this._ciphertext = value; }
        }

        internal bool IsSetCiphertext()
        {
            return this._ciphertext != null;
        }

        public AWS.EncryptionSDK.Core.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        internal bool IsSetMaterialsManager()
        {
            return this._materialsManager != null;
        }

        public AWS.EncryptionSDK.Core.IKeyring Keyring
        {
            get { return this._keyring; }
            set { this._keyring = value; }
        }

        internal bool IsSetKeyring()
        {
            return this._keyring != null;
        }

        public void Validate()
        {
            if (!IsSetCiphertext())
                throw new System.ArgumentException("Missing value for required property 'Ciphertext'");
        }
    }
}
