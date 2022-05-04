// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public class GetEncryptionMaterialsInput
    {
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private AWS.EncryptionSDK.Core.CommitmentPolicy _commitmentPolicy;
        private AWS.EncryptionSDK.Core.AlgorithmSuiteId _algorithmSuiteId;
        private long? _maxPlaintextLength;

        public System.Collections.Generic.Dictionary<string, string> EncryptionContext
        {
            get { return this._encryptionContext; }
            set { this._encryptionContext = value; }
        }

        internal bool IsSetEncryptionContext()
        {
            return this._encryptionContext != null;
        }

        public AWS.EncryptionSDK.Core.CommitmentPolicy CommitmentPolicy
        {
            get { return this._commitmentPolicy; }
            set { this._commitmentPolicy = value; }
        }

        internal bool IsSetCommitmentPolicy()
        {
            return this._commitmentPolicy != null;
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

        public long MaxPlaintextLength
        {
            get { return this._maxPlaintextLength.GetValueOrDefault(); }
            set { this._maxPlaintextLength = value; }
        }

        internal bool IsSetMaxPlaintextLength()
        {
            return this._maxPlaintextLength.HasValue;
        }

        public void Validate()
        {
            if (!IsSetEncryptionContext())
                throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
            if (!IsSetCommitmentPolicy())
                throw new System.ArgumentException("Missing value for required property 'CommitmentPolicy'");
        }
    }
}
