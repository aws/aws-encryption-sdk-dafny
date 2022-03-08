// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class DecryptOutput
    {
        private System.IO.MemoryStream _plaintext;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId;

        public System.IO.MemoryStream Plaintext
        {
            get { return this._plaintext; }
            set { this._plaintext = value; }
        }

        internal bool IsSetPlaintext()
        {
            return this._plaintext != null;
        }

        public System.Collections.Generic.Dictionary<string, string> EncryptionContext
        {
            get { return this._encryptionContext; }
            set { this._encryptionContext = value; }
        }

        internal bool IsSetEncryptionContext()
        {
            return this._encryptionContext != null;
        }

        public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId
        {
            get { return this._algorithmSuiteId; }
            set { this._algorithmSuiteId = value; }
        }

        internal bool IsSetAlgorithmSuiteId()
        {
            return this._algorithmSuiteId != null;
        }

        public void Validate()
        {
        }
    }
}
