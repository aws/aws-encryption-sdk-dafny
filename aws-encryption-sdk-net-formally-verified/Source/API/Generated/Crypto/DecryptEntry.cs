// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:21:59.652135

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class DecryptEntry
    {
        public System.IO.MemoryStream Identifier { get; private set; }
        public DecryptionMaterials DecryptionMaterials { get; private set; }
        public long CreationTime { get; private set; }
        public long ExpiryTime { get; private set; }
        public CacheUsageMetadata UsageMetadata { get; private set; }

        public static IDecryptEntryBuilder Builder()
        {
            return new DecryptEntryBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptEntryBuilder : IDecryptEntryBuilder
        {
            private System.IO.MemoryStream Identifier;
            private DecryptionMaterials DecryptionMaterials;
            private long? CreationTime;
            private long? ExpiryTime;
            private CacheUsageMetadata UsageMetadata;

            public IDecryptEntryBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public IDecryptEntryBuilder WithDecryptionMaterials(DecryptionMaterials value)
            {
                DecryptionMaterials = value;
                return this;
            }

            public IDecryptEntryBuilder WithCreationTime(long value)
            {
                CreationTime = value;
                return this;
            }

            public IDecryptEntryBuilder WithExpiryTime(long value)
            {
                ExpiryTime = value;
                return this;
            }

            public IDecryptEntryBuilder WithUsageMetadata(CacheUsageMetadata value)
            {
                UsageMetadata = value;
                return this;
            }

            public DecryptEntry Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                if (DecryptionMaterials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "decryptionMaterials"));
                }

                if (CreationTime == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "creationTime"));
                }

                if (ExpiryTime == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "expiryTime"));
                }

                if (UsageMetadata == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "usageMetadata"));
                }

                return new DecryptEntry
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                    DecryptionMaterials = (DecryptionMaterials) DecryptionMaterials, CreationTime = (long) CreationTime,
                    ExpiryTime = (long) ExpiryTime, UsageMetadata = (CacheUsageMetadata) UsageMetadata,
                };
            }
        }
    }

    public interface IDecryptEntryBuilder
    {
        IDecryptEntryBuilder WithIdentifier(System.IO.MemoryStream value);
        IDecryptEntryBuilder WithDecryptionMaterials(DecryptionMaterials value);
        IDecryptEntryBuilder WithCreationTime(long value);
        IDecryptEntryBuilder WithExpiryTime(long value);
        IDecryptEntryBuilder WithUsageMetadata(CacheUsageMetadata value);
        DecryptEntry Build();
    }
}
