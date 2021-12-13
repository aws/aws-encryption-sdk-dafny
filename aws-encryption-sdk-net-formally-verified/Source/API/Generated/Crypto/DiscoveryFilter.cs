// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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