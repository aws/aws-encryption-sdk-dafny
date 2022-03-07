// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateAwsKmsDiscoveryKeyringInput
    {
        private Amazon.KeyManagementService.IAmazonKeyManagementService _kmsClient;
        private Aws.Crypto.DiscoveryFilter _discoveryFilter;
        private System.Collections.Generic.List<string> _grantTokens;

        public Amazon.KeyManagementService.IAmazonKeyManagementService KmsClient
        {
            get { return this._kmsClient; }
            set { this._kmsClient = value; }
        }

        internal bool IsSetKmsClient()
        {
            return this._kmsClient != null;
        }

        public Aws.Crypto.DiscoveryFilter DiscoveryFilter
        {
            get { return this._discoveryFilter; }
            set { this._discoveryFilter = value; }
        }

        internal bool IsSetDiscoveryFilter()
        {
            return this._discoveryFilter != null;
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