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
    public class EncryptEntry
    {
        public System.IO.MemoryStream Identifier { get; private set; }
        public EncryptionMaterials EncryptionMaterials { get; private set; }
        public long CreationTime { get; private set; }
        public long ExpiryTime { get; private set; }
        public CacheUsageMetadata UsageMetadata { get; private set; }

        public static IEncryptEntryBuilder Builder()
        {
            return new EncryptEntryBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptEntryBuilder : IEncryptEntryBuilder
        {
            private System.IO.MemoryStream Identifier;
            private EncryptionMaterials EncryptionMaterials;
            private long? CreationTime;
            private long? ExpiryTime;
            private CacheUsageMetadata UsageMetadata;

            public IEncryptEntryBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public IEncryptEntryBuilder WithEncryptionMaterials(EncryptionMaterials value)
            {
                EncryptionMaterials = value;
                return this;
            }

            public IEncryptEntryBuilder WithCreationTime(long value)
            {
                CreationTime = value;
                return this;
            }

            public IEncryptEntryBuilder WithExpiryTime(long value)
            {
                ExpiryTime = value;
                return this;
            }

            public IEncryptEntryBuilder WithUsageMetadata(CacheUsageMetadata value)
            {
                UsageMetadata = value;
                return this;
            }

            public EncryptEntry Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                if (EncryptionMaterials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionMaterials"));
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

                return new EncryptEntry
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                    EncryptionMaterials = (EncryptionMaterials) EncryptionMaterials, CreationTime = (long) CreationTime,
                    ExpiryTime = (long) ExpiryTime, UsageMetadata = (CacheUsageMetadata) UsageMetadata,
                };
            }
        }
    }

    public interface IEncryptEntryBuilder
    {
        IEncryptEntryBuilder WithIdentifier(System.IO.MemoryStream value);
        IEncryptEntryBuilder WithEncryptionMaterials(EncryptionMaterials value);
        IEncryptEntryBuilder WithCreationTime(long value);
        IEncryptEntryBuilder WithExpiryTime(long value);
        IEncryptEntryBuilder WithUsageMetadata(CacheUsageMetadata value);
        EncryptEntry Build();
    }
}