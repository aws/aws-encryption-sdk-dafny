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
    public class GetEntryForDecryptOutput
    {
        private Aws.Crypto.DecryptEntry _cacheEntry;

        public Aws.Crypto.DecryptEntry CacheEntry
        {
            get { return this._cacheEntry; }
            set { this._cacheEntry = value; }
        }

        public void Validate()
        {
        }
    }
}
