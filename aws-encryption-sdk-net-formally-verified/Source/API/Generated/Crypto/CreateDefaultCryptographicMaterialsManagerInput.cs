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
    public class CreateDefaultCryptographicMaterialsManagerInput
    {
        private Aws.Crypto.IKeyring _keyring;

        public Aws.Crypto.IKeyring Keyring
        {
            get { return this._keyring; }
            set { this._keyring = value; }
        }

        public void Validate()
        {
        }
    }
}
