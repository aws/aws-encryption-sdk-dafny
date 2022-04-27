// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    public class EncryptInput
    {
        private System.IO.MemoryStream _plaintext;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private AWS.EncryptionSDK.Core.ICryptographicMaterialsManager _materialsManager;
        private AWS.EncryptionSDK.Core.IKeyring _keyring;
        private AWS.EncryptionSDK.Core.AlgorithmSuiteId _algorithmSuiteId;
        private long? _frameLength;

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

        public AWS.EncryptionSDK.Core.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        internal bool IsSetMaterialsManager()
        {
            return this._materialsManager != null;
        }

        public AWS.EncryptionSDK.Core.IKeyring Keyring
        {
            get { return this._keyring; }
            set { this._keyring = value; }
        }

        internal bool IsSetKeyring()
        {
            return this._keyring != null;
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

        public long FrameLength
        {
            get { return this._frameLength.GetValueOrDefault(); }
            set { this._frameLength = value; }
        }

        internal bool IsSetFrameLength()
        {
            return this._frameLength.HasValue;
        }

        public void Validate()
        {
            if (!IsSetPlaintext())
                throw new System.ArgumentException("Missing value for required property 'Plaintext'");
        }
    }
}
