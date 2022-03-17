// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public class CreateDefaultCryptographicMaterialsManagerInput
    {
        private Aws.EncryptionSdk.Core.IKeyring _keyring;

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
            if (!IsSetKeyring()) throw new System.ArgumentException("Missing value for required member 'keyring'");
        }
    }
}
