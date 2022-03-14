// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    public class GetClientInput
    {
        private string _region;

        public string Region
        {
            get { return this._region; }
            set { this._region = value; }
        }

        internal bool IsSetRegion()
        {
            return this._region != null;
        }

        public void Validate()
        {
            if (!IsSetRegion()) throw new System.ArgumentException("Missing value for required member 'region'");
        }
    }
}
