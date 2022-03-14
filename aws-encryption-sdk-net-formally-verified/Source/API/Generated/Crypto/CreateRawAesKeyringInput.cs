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

        internal bool IsSetKeyNamespace()
        {
            return this._keyNamespace != null;
        }

        public string KeyName
        {
            get { return this._keyName; }
            set { this._keyName = value; }
        }

        internal bool IsSetKeyName()
        {
            return this._keyName != null;
        }

        public System.IO.MemoryStream WrappingKey
        {
            get { return this._wrappingKey; }
            set { this._wrappingKey = value; }
        }

        internal bool IsSetWrappingKey()
        {
            return this._wrappingKey != null;
        }

        public Aws.Crypto.AesWrappingAlg WrappingAlg
        {
            get { return this._wrappingAlg; }
            set { this._wrappingAlg = value; }
        }

        internal bool IsSetWrappingAlg()
        {
            return this._wrappingAlg != null;
        }

        public void Validate()
        {
            if (!IsSetKeyNamespace())
                throw new System.ArgumentException("Missing value for required member 'keyNamespace'");
            if (!IsSetKeyName()) throw new System.ArgumentException("Missing value for required member 'keyName'");
            if (!IsSetWrappingKey())
                throw new System.ArgumentException("Missing value for required member 'wrappingKey'");
            if (!IsSetWrappingAlg())
                throw new System.ArgumentException("Missing value for required member 'wrappingAlg'");
        }
    }
}
