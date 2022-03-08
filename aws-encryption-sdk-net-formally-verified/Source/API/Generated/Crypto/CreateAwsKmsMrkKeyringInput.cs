// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateAwsKmsMrkKeyringInput
    {
        private string _kmsKeyId;
        private Amazon.KeyManagementService.IAmazonKeyManagementService _kmsClient;
        private System.Collections.Generic.List<string> _grantTokens;

        public string KmsKeyId
        {
            get { return this._kmsKeyId; }
            set { this._kmsKeyId = value; }
        }

        internal bool IsSetKmsKeyId()
        {
            return this._kmsKeyId != null;
        }

        public Amazon.KeyManagementService.IAmazonKeyManagementService KmsClient
        {
            get { return this._kmsClient; }
            set { this._kmsClient = value; }
        }

        internal bool IsSetKmsClient()
        {
            return this._kmsClient != null;
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
