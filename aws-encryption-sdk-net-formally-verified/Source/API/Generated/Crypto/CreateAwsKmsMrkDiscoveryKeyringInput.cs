// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateAwsKmsMrkDiscoveryKeyringInput
    {
        private Amazon.KeyManagementService.IAmazonKeyManagementService _kmsClient;
        private Aws.Crypto.DiscoveryFilter _discoveryFilter;
        private System.Collections.Generic.List<string> _grantTokens;
        private string _region;

        public Amazon.KeyManagementService.IAmazonKeyManagementService KmsClient
        {
            get { return this._kmsClient; }
            set { this._kmsClient = value; }
        }

        public Aws.Crypto.DiscoveryFilter DiscoveryFilter
        {
            get { return this._discoveryFilter; }
            set { this._discoveryFilter = value; }
        }

        public System.Collections.Generic.List<string> GrantTokens
        {
            get { return this._grantTokens; }
            set { this._grantTokens = value; }
        }

        public string Region
        {
            get { return this._region; }
            set { this._region = value; }
        }

        public void Validate()
        {
        }
    }
}
