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

        internal bool IsSetAlgorithmSuiteId()
        {
            return this._algorithmSuiteId != null;
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

        public System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> EncryptedDataKeys
        {
            get { return this._encryptedDataKeys; }
            set { this._encryptedDataKeys = value; }
        }

        internal bool IsSetEncryptedDataKeys()
        {
            return this._encryptedDataKeys != null;
        }

        public System.IO.MemoryStream PlaintextDataKey
        {
            get { return this._plaintextDataKey; }
            set { this._plaintextDataKey = value; }
        }

        internal bool IsSetPlaintextDataKey()
        {
            return this._plaintextDataKey != null;
        }

        public System.IO.MemoryStream SigningKey
        {
            get { return this._signingKey; }
            set { this._signingKey = value; }
        }

        internal bool IsSetSigningKey()
        {
            return this._signingKey != null;
        }

        public void Validate()
        {
            if (!IsSetAlgorithmSuiteId())
                throw new System.ArgumentException("Missing value for required member 'algorithmSuiteId'");
            if (!IsSetEncryptionContext())
                throw new System.ArgumentException("Missing value for required member 'encryptionContext'");
            if (!IsSetEncryptedDataKeys())
                throw new System.ArgumentException("Missing value for required member 'encryptedDataKeys'");
        }
    }
}
