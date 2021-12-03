// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:12:30.370597

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

        public System.IO.MemoryStream Ciphertext
        {
            get { return this._ciphertext; }
            set { this._ciphertext = value; }
        }

        public Aws.Crypto.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        public void Validate()
        {
        }
    }
}
