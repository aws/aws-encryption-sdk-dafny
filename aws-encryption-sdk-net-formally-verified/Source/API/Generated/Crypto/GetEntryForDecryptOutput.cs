// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEntryForDecryptOutput
    {
        public DecryptEntry CacheEntry { get; private set; }

        public static IGetEntryForDecryptOutputBuilder Builder()
        {
            return new GetEntryForDecryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEntryForDecryptOutputBuilder : IGetEntryForDecryptOutputBuilder
        {
            private DecryptEntry CacheEntry;

            public IGetEntryForDecryptOutputBuilder WithCacheEntry(DecryptEntry value)
            {
                CacheEntry = value;
                return this;
            }

            public GetEntryForDecryptOutput Build()
            {
                if (CacheEntry == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "cacheEntry"));
                }

                return new GetEntryForDecryptOutput
                {
                    CacheEntry = (DecryptEntry) CacheEntry,
                };
            }
        }
    }

    public interface IGetEntryForDecryptOutputBuilder
    {
        IGetEntryForDecryptOutputBuilder WithCacheEntry(DecryptEntry value);
        GetEntryForDecryptOutput Build();
    }
}