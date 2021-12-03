// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:30:30.159384

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DecryptionMaterials
    {
        private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private System.IO.MemoryStream _plaintextDataKey;
        private System.IO.MemoryStream _verificationKey;

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

        public System.IO.MemoryStream PlaintextDataKey
        {
            get { return this._plaintextDataKey; }
            set { this._plaintextDataKey = value; }
        }

        public System.IO.MemoryStream VerificationKey
        {
            get { return this._verificationKey; }
            set { this._verificationKey = value; }
        }

        public void Validate()
        {
        }
    }
}
