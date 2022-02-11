// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateDefaultClientSupplierOutput
    {
        private Aws.Crypto.IClientSupplier _clientSupplier;

        public Aws.Crypto.IClientSupplier ClientSupplier
        {
            get { return this._clientSupplier; }
            set { this._clientSupplier = value; }
        }

        public void Validate()
        {
        }
    }
}