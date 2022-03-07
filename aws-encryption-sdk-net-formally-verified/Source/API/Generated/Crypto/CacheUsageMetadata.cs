// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CacheUsageMetadata
    {
        private long? _messageUsage;
        private long? _byteUsage;

        public long MessageUsage
        {
            get { return this._messageUsage.GetValueOrDefault(); }
            set { this._messageUsage = value; }
        }

        internal bool IsSetMessageUsage()
        {
            return this._messageUsage.HasValue;
        }

        public long ByteUsage
        {
            get { return this._byteUsage.GetValueOrDefault(); }
            set { this._byteUsage = value; }
        }

        internal bool IsSetByteUsage()
        {
            return this._byteUsage.HasValue;
        }

        public void Validate()
        {
        }
    }
}
