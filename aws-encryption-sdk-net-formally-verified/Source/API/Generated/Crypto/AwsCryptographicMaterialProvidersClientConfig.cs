// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class AwsCryptographicMaterialProvidersClientConfig
    {
        private Aws.Crypto.ConfigurationDefaults _configDefaults;

        public Aws.Crypto.ConfigurationDefaults ConfigDefaults
        {
            get { return this._configDefaults; }
            set { this._configDefaults = value; }
        }

        internal bool IsSetConfigDefaults()
        {
            return this._configDefaults != null;
        }

        public void Validate()
        {
        }
    }
}
