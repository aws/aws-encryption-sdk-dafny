// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class EncryptInput
    {
        private System.IO.MemoryStream _plaintext;
        private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
        private Aws.Crypto.ICryptographicMaterialsManager _materialsManager;
        private Aws.Crypto.IKeyring _keyring;
        private Aws.Crypto.AlgorithmSuiteId _algorithmSuiteId;
        private long? _frameLength;
        private long? _maxPlaintextLength;

        public System.IO.MemoryStream Plaintext
        {
            get { return this._plaintext; }
            set { this._plaintext = value; }
        }

        public System.Collections.Generic.Dictionary<string, string> EncryptionContext
        {
            get { return this._encryptionContext; }
            set { this._encryptionContext = value; }
        }

        public Aws.Crypto.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        public Aws.Crypto.IKeyring Keyring
        {
            get { return this._keyring; }
            set { this._keyring = value; }
        }

        public Aws.Crypto.AlgorithmSuiteId AlgorithmSuiteId
        {
            get { return this._algorithmSuiteId; }
            set { this._algorithmSuiteId = value; }
        }

        public long FrameLength
        {
            get { return this._frameLength.GetValueOrDefault(); }
            set { this._frameLength = value; }
        }

        public long MaxPlaintextLength
        {
            get { return this._maxPlaintextLength.GetValueOrDefault(); }
            set { this._maxPlaintextLength = value; }
        }

        public void Validate()
        {
        }
    }
}
