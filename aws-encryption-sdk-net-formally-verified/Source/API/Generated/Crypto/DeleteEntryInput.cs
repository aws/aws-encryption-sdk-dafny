// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DeleteEntryInput
    {
        private System.IO.MemoryStream _identifier;

        public System.IO.MemoryStream Identifier
        {
            get { return this._identifier; }
            set { this._identifier = value; }
        }

        internal bool IsSetIdentifier()
        {
            return this._identifier != null;
        }

        public void Validate()
        {
        }
    }
}
