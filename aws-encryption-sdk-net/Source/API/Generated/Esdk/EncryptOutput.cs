// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    public class EncryptOutput
    {
        private System.IO.MemoryStream _ciphertext;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private AWS.EncryptionSDK.Core.AlgorithmSuiteId _algorithmSuiteId;

        public System.IO.MemoryStream Ciphertext
        {
            get { return this._ciphertext; }
            set { this._ciphertext = value; }
        }

        internal bool IsSetCiphertext()
        {
            return this._ciphertext != null;
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

        public AWS.EncryptionSDK.Core.AlgorithmSuiteId AlgorithmSuiteId
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
            if (!IsSetCiphertext())
                throw new System.ArgumentException("Missing value for required property 'Ciphertext'");
            if (!IsSetEncryptionContext())
                throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
            if (!IsSetAlgorithmSuiteId())
                throw new System.ArgumentException("Missing value for required property 'AlgorithmSuiteId'");
        }
    }
}
