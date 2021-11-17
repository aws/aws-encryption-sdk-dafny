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
    public class CreateCachingCryptographicMaterialsManagerInput
    {
        public ICryptoMaterialsCache Cache { get; private set; }
        public int CacheLimitTtl { get; private set; }
        public IKeyring Keyring { get; private set; }
        public ICryptographicMaterialsManager MaterialsManager { get; private set; }
        public string PartitionId { get; private set; }
        public long? LimitBytes { get; private set; }
        public long? LimitMessages { get; private set; }

        public static ICreateCachingCryptographicMaterialsManagerInputBuilder Builder()
        {
            return new CreateCachingCryptographicMaterialsManagerInputBuilder();
        }

        public void Validate()
        {
        }

        private class
            CreateCachingCryptographicMaterialsManagerInputBuilder :
                ICreateCachingCryptographicMaterialsManagerInputBuilder
        {
            private ICryptoMaterialsCache Cache;
            private int? CacheLimitTtl;
            private IKeyring Keyring;
            private ICryptographicMaterialsManager MaterialsManager;
            private string PartitionId;
            private long? LimitBytes;
            private long? LimitMessages;

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithCache(ICryptoMaterialsCache value)
            {
                Cache = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithCacheLimitTtl(int value)
            {
                CacheLimitTtl = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithKeyring(IKeyring value)
            {
                Keyring = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithMaterialsManager(
                ICryptographicMaterialsManager value)
            {
                MaterialsManager = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithPartitionId(string value)
            {
                PartitionId = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithLimitBytes(long? value)
            {
                LimitBytes = value;
                return this;
            }

            public ICreateCachingCryptographicMaterialsManagerInputBuilder WithLimitMessages(long? value)
            {
                LimitMessages = value;
                return this;
            }

            public CreateCachingCryptographicMaterialsManagerInput Build()
            {
                if (Cache == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "cache"));
                }

                if (CacheLimitTtl == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "cacheLimitTtl"));
                }

                return new CreateCachingCryptographicMaterialsManagerInput
                {
                    Cache = (ICryptoMaterialsCache) Cache, CacheLimitTtl = (int) CacheLimitTtl,
                    Keyring = (IKeyring) Keyring, MaterialsManager = (ICryptographicMaterialsManager) MaterialsManager,
                    PartitionId = (string) PartitionId, LimitBytes = (long?) LimitBytes,
                    LimitMessages = (long?) LimitMessages,
                };
            }
        }
    }

    public interface ICreateCachingCryptographicMaterialsManagerInputBuilder
    {
        ICreateCachingCryptographicMaterialsManagerInputBuilder WithCache(ICryptoMaterialsCache value);
        ICreateCachingCryptographicMaterialsManagerInputBuilder WithCacheLimitTtl(int value);
        ICreateCachingCryptographicMaterialsManagerInputBuilder WithKeyring(IKeyring value);

        ICreateCachingCryptographicMaterialsManagerInputBuilder WithMaterialsManager(
            ICryptographicMaterialsManager value);

        ICreateCachingCryptographicMaterialsManagerInputBuilder WithPartitionId(string value);
        ICreateCachingCryptographicMaterialsManagerInputBuilder WithLimitBytes(long? value);
        ICreateCachingCryptographicMaterialsManagerInputBuilder WithLimitMessages(long? value);
        CreateCachingCryptographicMaterialsManagerInput Build();
    }
}