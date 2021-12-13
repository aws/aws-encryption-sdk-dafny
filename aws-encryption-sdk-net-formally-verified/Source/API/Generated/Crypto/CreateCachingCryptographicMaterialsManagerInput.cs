// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateCachingCryptographicMaterialsManagerInput
    {
        private Aws.Crypto.ICryptoMaterialsCache _cache;
        private int? _cacheLimitTtl;
        private Aws.Crypto.IKeyring _keyring;
        private Aws.Crypto.ICryptographicMaterialsManager _materialsManager;
        private string _partitionId;
        private long? _limitBytes;
        private long? _limitMessages;

        public Aws.Crypto.ICryptoMaterialsCache Cache
        {
            get { return this._cache; }
            set { this._cache = value; }
        }

        public int CacheLimitTtl
        {
            get { return this._cacheLimitTtl.GetValueOrDefault(); }
            set { this._cacheLimitTtl = value; }
        }

        public Aws.Crypto.IKeyring Keyring
        {
            get { return this._keyring; }
            set { this._keyring = value; }
        }

        public Aws.Crypto.ICryptographicMaterialsManager MaterialsManager
        {
            get { return this._materialsManager; }
            set { this._materialsManager = value; }
        }

        public string PartitionId
        {
            get { return this._partitionId; }
            set { this._partitionId = value; }
        }

        public long LimitBytes
        {
            get { return this._limitBytes.GetValueOrDefault(); }
            set { this._limitBytes = value; }
        }

        public long LimitMessages
        {
            get { return this._limitMessages.GetValueOrDefault(); }
            set { this._limitMessages = value; }
        }

        public void Validate()
        {
        }
    }
}