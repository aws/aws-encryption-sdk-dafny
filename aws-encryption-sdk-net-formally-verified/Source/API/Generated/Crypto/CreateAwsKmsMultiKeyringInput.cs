// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    public class CreateAwsKmsMultiKeyringInput
    {
        private string _generator;
        private System.Collections.Generic.List<string> _kmsKeyIds;
        private Aws.EncryptionSdk.Core.IClientSupplier _clientSupplier;
        private System.Collections.Generic.List<string> _grantTokens;

        public string Generator
        {
            get { return this._generator; }
            set { this._generator = value; }
        }

        internal bool IsSetGenerator()
        {
            return this._generator != null;
        }

        public System.Collections.Generic.List<string> KmsKeyIds
        {
            get { return this._kmsKeyIds; }
            set { this._kmsKeyIds = value; }
        }

        internal bool IsSetKmsKeyIds()
        {
            return this._kmsKeyIds != null;
        }

        public Aws.EncryptionSdk.Core.IClientSupplier ClientSupplier
        {
            get { return this._clientSupplier; }
            set { this._clientSupplier = value; }
        }

        internal bool IsSetClientSupplier()
        {
            return this._clientSupplier != null;
        }

        public System.Collections.Generic.List<string> GrantTokens
        {
            get { return this._grantTokens; }
            set { this._grantTokens = value; }
        }

        internal bool IsSetGrantTokens()
        {
            return this._grantTokens != null;
        }

        public void Validate()
        {
        }
    }
}
