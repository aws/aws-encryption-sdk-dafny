// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateMultiKeyringInput
    {
        private Aws.Crypto.IKeyring _generator;
        private System.Collections.Generic.List<Aws.Crypto.IKeyring> _childKeyrings;

        public Aws.Crypto.IKeyring Generator
        {
            get { return this._generator; }
            set { this._generator = value; }
        }

        internal bool IsSetGenerator()
        {
            return this._generator != null;
        }

        public System.Collections.Generic.List<Aws.Crypto.IKeyring> ChildKeyrings
        {
            get { return this._childKeyrings; }
            set { this._childKeyrings = value; }
        }

        internal bool IsSetChildKeyrings()
        {
            return this._childKeyrings != null;
        }

        public void Validate()
        {
        }
    }
}