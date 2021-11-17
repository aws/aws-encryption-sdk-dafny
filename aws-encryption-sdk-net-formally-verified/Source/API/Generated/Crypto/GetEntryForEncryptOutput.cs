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
    public class GetEntryForEncryptOutput
    {
        public EncryptEntry CacheEntry { get; private set; }

        public static IGetEntryForEncryptOutputBuilder Builder()
        {
            return new GetEntryForEncryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEntryForEncryptOutputBuilder : IGetEntryForEncryptOutputBuilder
        {
            private EncryptEntry CacheEntry;

            public IGetEntryForEncryptOutputBuilder WithCacheEntry(EncryptEntry value)
            {
                CacheEntry = value;
                return this;
            }

            public GetEntryForEncryptOutput Build()
            {
                if (CacheEntry == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "cacheEntry"));
                }

                return new GetEntryForEncryptOutput
                {
                    CacheEntry = (EncryptEntry) CacheEntry,
                };
            }
        }
    }

    public interface IGetEntryForEncryptOutputBuilder
    {
        IGetEntryForEncryptOutputBuilder WithCacheEntry(EncryptEntry value);
        GetEntryForEncryptOutput Build();
    }
}