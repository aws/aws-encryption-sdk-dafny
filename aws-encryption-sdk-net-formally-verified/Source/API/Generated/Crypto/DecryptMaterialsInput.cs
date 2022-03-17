// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public class DecryptMaterialsInput
    {
        private Aws.EncryptionSdk.Core.AlgorithmSuiteId _algorithmSuiteId;
        private Aws.EncryptionSdk.Core.CommitmentPolicy _commitmentPolicy;
        private System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> _encryptedDataKeys;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;

        public Aws.EncryptionSdk.Core.AlgorithmSuiteId AlgorithmSuiteId
        {
            get { return this._algorithmSuiteId; }
            set { this._algorithmSuiteId = value; }
        }

        internal bool IsSetAlgorithmSuiteId()
        {
            return this._algorithmSuiteId != null;
        }

        public Aws.EncryptionSdk.Core.CommitmentPolicy CommitmentPolicy
        {
            get { return this._commitmentPolicy; }
            set { this._commitmentPolicy = value; }
        }

        internal bool IsSetCommitmentPolicy()
        {
            return this._commitmentPolicy != null;
        }

        public System.Collections.Generic.List<Aws.EncryptionSdk.Core.EncryptedDataKey> EncryptedDataKeys
        {
            get { return this._encryptedDataKeys; }
            set { this._encryptedDataKeys = value; }
        }

        internal bool IsSetEncryptedDataKeys()
        {
            return this._encryptedDataKeys != null;
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

        public void Validate()
        {
            if (!IsSetAlgorithmSuiteId())
                throw new System.ArgumentException("Missing value for required member 'algorithmSuiteId'");
            if (!IsSetCommitmentPolicy())
                throw new System.ArgumentException("Missing value for required member 'commitmentPolicy'");
            if (!IsSetEncryptedDataKeys())
                throw new System.ArgumentException("Missing value for required member 'encryptedDataKeys'");
            if (!IsSetEncryptionContext())
                throw new System.ArgumentException("Missing value for required member 'encryptionContext'");
        }
    }
}
