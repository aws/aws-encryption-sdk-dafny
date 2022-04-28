// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
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
            if (!IsSetRegion()) throw new System.ArgumentException("Missing value for required property 'Region'");
        }
    }
}
