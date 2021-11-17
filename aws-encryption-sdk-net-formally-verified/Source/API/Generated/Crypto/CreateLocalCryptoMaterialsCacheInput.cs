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
    public class CreateLocalCryptoMaterialsCacheInput
    {
        public int EntryCapacity { get; private set; }
        public int? EntryPruningTailSize { get; private set; }

        public static ICreateLocalCryptoMaterialsCacheInputBuilder Builder()
        {
            return new CreateLocalCryptoMaterialsCacheInputBuilder();
        }

        public void Validate()
        {
        }

        private class CreateLocalCryptoMaterialsCacheInputBuilder : ICreateLocalCryptoMaterialsCacheInputBuilder
        {
            private int? EntryCapacity;
            private int? EntryPruningTailSize;

            public ICreateLocalCryptoMaterialsCacheInputBuilder WithEntryCapacity(int value)
            {
                EntryCapacity = value;
                return this;
            }

            public ICreateLocalCryptoMaterialsCacheInputBuilder WithEntryPruningTailSize(int? value)
            {
                EntryPruningTailSize = value;
                return this;
            }

            public CreateLocalCryptoMaterialsCacheInput Build()
            {
                if (EntryCapacity == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "entryCapacity"));
                }

                return new CreateLocalCryptoMaterialsCacheInput
                {
                    EntryCapacity = (int) EntryCapacity, EntryPruningTailSize = (int?) EntryPruningTailSize,
                };
            }
        }
    }

    public interface ICreateLocalCryptoMaterialsCacheInputBuilder
    {
        ICreateLocalCryptoMaterialsCacheInputBuilder WithEntryCapacity(int value);
        ICreateLocalCryptoMaterialsCacheInputBuilder WithEntryPruningTailSize(int? value);
        CreateLocalCryptoMaterialsCacheInput Build();
    }
}