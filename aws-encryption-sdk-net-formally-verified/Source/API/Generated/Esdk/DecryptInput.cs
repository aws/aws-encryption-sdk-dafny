// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk
    ;

namespace Aws.EncryptionSdk
{
    public class DecryptInput
    {
        private System.IO.MemoryStream _ciphertext;
        private Aws.EncryptionSdk.Core.ICryptographicMaterialsManager _materialsManager;
        private Aws.EncryptionSdk.Core.IKeyring _keyring;

        public System.IO.MemoryStream Ciphertext
        {
            get { return this._ciphertext; }
            set { this._ciphertext = value; }
        }

        internal bool IsSetCiphertext()
        {
            return this._ciphertext != null;
        }

        public Aws.EncryptionSdk.Core.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        internal bool IsSetMaterialsManager()
        {
            return this._materialsManager != null;
        }

        public Aws.EncryptionSdk.Core.IKeyring Keyring
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
                throw new System.ArgumentException("Missing value for required member 'ciphertext'");
        }
    }
}
