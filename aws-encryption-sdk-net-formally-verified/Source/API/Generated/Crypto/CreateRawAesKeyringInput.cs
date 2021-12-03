// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateRawAesKeyringInput
    {
        private string _keyNamespace;
        private string _keyName;
        private System.IO.MemoryStream _wrappingKey;
        private Aws.Crypto.AesWrappingAlg _wrappingAlg;

        public string KeyNamespace
        {
            get { return this._keyNamespace; }
            set { this._keyNamespace = value; }
        }

        public string KeyName
        {
            get { return this._keyName; }
            set { this._keyName = value; }
        }

        public System.IO.MemoryStream WrappingKey
        {
            get { return this._wrappingKey; }
            set { this._wrappingKey = value; }
        }

        public Aws.Crypto.AesWrappingAlg WrappingAlg
        {
            get { return this._wrappingAlg; }
            set { this._wrappingAlg = value; }
        }

        public void Validate()
        {
        }
    }
}
