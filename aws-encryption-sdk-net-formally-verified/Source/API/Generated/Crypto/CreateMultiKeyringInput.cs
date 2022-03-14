// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public class CreateMultiKeyringInput
    {
        private Aws.Encryption.Core.IKeyring _generator;
        private System.Collections.Generic.List<Aws.Encryption.Core.IKeyring> _childKeyrings;

        public Aws.Encryption.Core.IKeyring Generator
        {
            get { return this._generator; }
            set { this._generator = value; }
        }

        internal bool IsSetGenerator()
        {
            return this._generator != null;
        }

        public System.Collections.Generic.List<Aws.Encryption.Core.IKeyring> ChildKeyrings
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
            if (!IsSetChildKeyrings())
                throw new System.ArgumentException("Missing value for required member 'childKeyrings'");
        }
    }
}
