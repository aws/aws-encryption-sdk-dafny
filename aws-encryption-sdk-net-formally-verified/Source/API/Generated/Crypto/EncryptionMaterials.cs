// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class EncryptionMaterials
    {
        private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> _encryptedDataKeys;
        private System.IO.MemoryStream _plaintextDataKey;
        private System.IO.MemoryStream _signingKey;

        public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId
        {
            get { return this._algorithmSuiteId; }
            set { this._algorithmSuiteId = value; }
        }

        public System.Collections.Generic.Dictionary<string, string> EncryptionContext
        {
            get { return this._encryptionContext; }
            set { this._encryptionContext = value; }
        }

        public System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> EncryptedDataKeys
        {
            get { return this._encryptedDataKeys; }
            set { this._encryptedDataKeys = value; }
        }

        public System.IO.MemoryStream PlaintextDataKey
        {
            get { return this._plaintextDataKey; }
            set { this._plaintextDataKey = value; }
        }

        public System.IO.MemoryStream SigningKey
        {
            get { return this._signingKey; }
            set { this._signingKey = value; }
        }

        public void Validate()
        {
        }
    }
}