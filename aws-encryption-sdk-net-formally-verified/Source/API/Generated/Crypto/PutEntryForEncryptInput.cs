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
    public class PutEntryForEncryptInput
    {
        public System.IO.MemoryStream Identifier { get; private set; }
        public EncryptionMaterials EncryptionMaterials { get; private set; }
        public CacheUsageMetadata UsageMetadata { get; private set; }

        public static IPutEntryForEncryptInputBuilder Builder()
        {
            return new PutEntryForEncryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class PutEntryForEncryptInputBuilder : IPutEntryForEncryptInputBuilder
        {
            private System.IO.MemoryStream Identifier;
            private EncryptionMaterials EncryptionMaterials;
            private CacheUsageMetadata UsageMetadata;

            public IPutEntryForEncryptInputBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public IPutEntryForEncryptInputBuilder WithEncryptionMaterials(EncryptionMaterials value)
            {
                EncryptionMaterials = value;
                return this;
            }

            public IPutEntryForEncryptInputBuilder WithUsageMetadata(CacheUsageMetadata value)
            {
                UsageMetadata = value;
                return this;
            }

            public PutEntryForEncryptInput Build()
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

                if (UsageMetadata == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "usageMetadata"));
                }

                return new PutEntryForEncryptInput
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                    EncryptionMaterials = (EncryptionMaterials) EncryptionMaterials,
                    UsageMetadata = (CacheUsageMetadata) UsageMetadata,
                };
            }
        }
    }

    public interface IPutEntryForEncryptInputBuilder
    {
        IPutEntryForEncryptInputBuilder WithIdentifier(System.IO.MemoryStream value);
        IPutEntryForEncryptInputBuilder WithEncryptionMaterials(EncryptionMaterials value);
        IPutEntryForEncryptInputBuilder WithUsageMetadata(CacheUsageMetadata value);
        PutEntryForEncryptInput Build();
    }
}