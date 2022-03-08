// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEntryForEncryptOutput
    {
        private Aws.Crypto.EncryptEntry _cacheEntry;

        public Aws.Crypto.EncryptEntry CacheEntry
        {
            get { return this._cacheEntry; }
            set { this._cacheEntry = value; }
        }

        internal bool IsSetCacheEntry()
        {
            return this._cacheEntry != null;
        }

        public void Validate()
        {
        }
    }
}
