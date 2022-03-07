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
        private System.Collections.Generic.List<string> _accountIds;
        private string _partition;

        public System.Collections.Generic.List<string> AccountIds
        {
            get { return this._accountIds; }
            set { this._accountIds = value; }
        }

        internal bool IsSetAccountIds()
        {
            return this._accountIds != null;
        }

        public string Partition
        {
            get { return this._partition; }
            set { this._partition = value; }
        }

        internal bool IsSetPartition()
        {
            return this._partition != null;
        }

        public void Validate()
        {
        }
    }
}