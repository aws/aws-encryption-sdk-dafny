// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public class CreateMultiKeyringInput
    {
        private AWS.EncryptionSDK.Core.IKeyring _generator;
        private System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring> _childKeyrings;

        public AWS.EncryptionSDK.Core.IKeyring Generator
        {
            get { return this._generator; }
            set { this._generator = value; }
        }

        internal bool IsSetGenerator()
        {
            return this._generator != null;
        }

        public System.Collections.Generic.List<AWS.EncryptionSDK.Core.IKeyring> ChildKeyrings
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
                throw new System.ArgumentException("Missing value for required property 'ChildKeyrings'");
        }
    }
}
