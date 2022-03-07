// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class EncryptEntry
    {
        private System.IO.MemoryStream _identifier;
        private Aws.Crypto.EncryptionMaterials _encryptionMaterials;
        private long? _creationTime;
        private long? _expiryTime;
        private Aws.Crypto.CacheUsageMetadata _usageMetadata;

        public System.IO.MemoryStream Identifier
        {
            get { return this._identifier; }
            set { this._identifier = value; }
        }

        internal bool IsSetIdentifier()
        {
            return this._identifier != null;
        }

        public Aws.Crypto.EncryptionMaterials EncryptionMaterials
        {
            get { return this._encryptionMaterials; }
            set { this._encryptionMaterials = value; }
        }

        internal bool IsSetEncryptionMaterials()
        {
            return this._encryptionMaterials != null;
        }

        public long CreationTime
        {
            get { return this._creationTime.GetValueOrDefault(); }
            set { this._creationTime = value; }
        }

        internal bool IsSetCreationTime()
        {
            return this._creationTime.HasValue;
        }

        public long ExpiryTime
        {
            get { return this._expiryTime.GetValueOrDefault(); }
            set { this._expiryTime = value; }
        }

        internal bool IsSetExpiryTime()
        {
            return this._expiryTime.HasValue;
        }

        public Aws.Crypto.CacheUsageMetadata UsageMetadata
        {
            get { return this._usageMetadata; }
            set { this._usageMetadata = value; }
        }

        internal bool IsSetUsageMetadata()
        {
            return this._usageMetadata != null;
        }

        public void Validate()
        {
        }
    }
}