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
    public class CacheUsageMetadata
    {
        public long MessageUsage { get; private set; }
        public long ByteUsage { get; private set; }

        public static ICacheUsageMetadataBuilder Builder()
        {
            return new CacheUsageMetadataBuilder();
        }

        public void Validate()
        {
        }

        private class CacheUsageMetadataBuilder : ICacheUsageMetadataBuilder
        {
            private long? MessageUsage;
            private long? ByteUsage;

            public ICacheUsageMetadataBuilder WithMessageUsage(long value)
            {
                MessageUsage = value;
                return this;
            }

            public ICacheUsageMetadataBuilder WithByteUsage(long value)
            {
                ByteUsage = value;
                return this;
            }

            public CacheUsageMetadata Build()
            {
                if (MessageUsage == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "messageUsage"));
                }

                if (ByteUsage == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "byteUsage"));
                }

                return new CacheUsageMetadata
                {
                    MessageUsage = (long) MessageUsage, ByteUsage = (long) ByteUsage,
                };
            }
        }
    }

    public interface ICacheUsageMetadataBuilder
    {
        ICacheUsageMetadataBuilder WithMessageUsage(long value);
        ICacheUsageMetadataBuilder WithByteUsage(long value);
        CacheUsageMetadata Build();
    }
}