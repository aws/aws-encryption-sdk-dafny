// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEntryForDecryptOutput
    {
        private Aws.Crypto.DecryptEntry _cacheEntry;

        public Aws.Crypto.DecryptEntry CacheEntry
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