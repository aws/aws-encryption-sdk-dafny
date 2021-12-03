// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:30:30.159384

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DiscoveryFilter
    {
        private string _region;
        private string _partition;

        public string Region
        {
            get { return this._region; }
            set { this._region = value; }
        }

        public string Partition
        {
            get { return this._partition; }
            set { this._partition = value; }
        }

        public void Validate()
        {
        }
    }
}
