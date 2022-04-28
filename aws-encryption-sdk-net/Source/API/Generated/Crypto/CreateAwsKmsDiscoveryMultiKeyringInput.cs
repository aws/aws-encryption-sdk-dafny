// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public class CreateAwsKmsDiscoveryMultiKeyringInput
    {
        private System.Collections.Generic.List<string> _regions;
        private AWS.EncryptionSDK.Core.DiscoveryFilter _discoveryFilter;
        private AWS.EncryptionSDK.Core.IClientSupplier _clientSupplier;
        private System.Collections.Generic.List<string> _grantTokens;

        public System.Collections.Generic.List<string> Regions
        {
            get { return this._regions; }
            set { this._regions = value; }
        }

        internal bool IsSetRegions()
        {
            return this._regions != null;
        }

        public AWS.EncryptionSDK.Core.DiscoveryFilter DiscoveryFilter
        {
            get { return this._discoveryFilter; }
            set { this._discoveryFilter = value; }
        }

        internal bool IsSetDiscoveryFilter()
        {
            return this._discoveryFilter != null;
        }

        public AWS.EncryptionSDK.Core.IClientSupplier ClientSupplier
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
            if (!IsSetRegions()) throw new System.ArgumentException("Missing value for required property 'Regions'");
        }
    }
}
