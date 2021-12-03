// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DecryptMaterialsInput
    {
        private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId;
        private System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> _encryptedDataKeys;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;

        public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId
        {
            get { return this._algorithmSuiteId; }
            set { this._algorithmSuiteId = value; }
        }

        public System.Collections.Generic.List<Aws.Crypto.EncryptedDataKey> EncryptedDataKeys
        {
            get { return this._encryptedDataKeys; }
            set { this._encryptedDataKeys = value; }
        }

        public System.Collections.Generic.Dictionary<string, string> EncryptionContext
        {
            get { return this._encryptionContext; }
            set { this._encryptionContext = value; }
        }

        public void Validate()
        {
        }
    }
}
