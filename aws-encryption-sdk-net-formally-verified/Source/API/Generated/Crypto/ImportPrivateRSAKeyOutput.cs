// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class ImportPrivateRSAKeyOutput
    {
        private Aws.Crypto.IKey _key;

        public Aws.Crypto.IKey Key
        {
            get { return this._key; }
            set { this._key = value; }
        }

        public void Validate()
        {
        }
    }
}