// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class DecryptInput
    {
        private System.IO.MemoryStream _ciphertext;
        private Aws.Crypto.ICryptographicMaterialsManager _materialsManager;
        private Aws.Crypto.IKeyring _keyring;

        public System.IO.MemoryStream Ciphertext
        {
            get { return this._ciphertext; }
            set { this._ciphertext = value; }
        }

        internal bool IsSetCiphertext()
        {
            return this._ciphertext != null;
        }

        public Aws.Crypto.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        internal bool IsSetMaterialsManager()
        {
            return this._materialsManager != null;
        }

        public Aws.Crypto.IKeyring Keyring
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
        }
    }
}
