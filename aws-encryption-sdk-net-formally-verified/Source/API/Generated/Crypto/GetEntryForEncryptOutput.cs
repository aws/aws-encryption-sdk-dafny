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
    public class GetEntryForEncryptOutput
    {
        private Aws.Crypto.EncryptEntry _cacheEntry;

        public Aws.Crypto.EncryptEntry CacheEntry
        {
            get { return this._cacheEntry; }
            set { this._cacheEntry = value; }
        }

        public void Validate()
        {
        }
    }
}
