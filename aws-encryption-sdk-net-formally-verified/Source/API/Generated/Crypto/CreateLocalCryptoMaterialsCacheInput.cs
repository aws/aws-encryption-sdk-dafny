// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class CreateLocalCryptoMaterialsCacheInput
    {
        private int? _entryCapacity;
        private int? _entryPruningTailSize;

        public int EntryCapacity
        {
            get { return this._entryCapacity.GetValueOrDefault(); }
            set { this._entryCapacity = value; }
        }

        internal bool IsSetEntryCapacity()
        {
            return this._entryCapacity.HasValue;
        }

        public int EntryPruningTailSize
        {
            get { return this._entryPruningTailSize.GetValueOrDefault(); }
            set { this._entryPruningTailSize = value; }
        }

        internal bool IsSetEntryPruningTailSize()
        {
            return this._entryPruningTailSize.HasValue;
        }

        public void Validate()
        {
        }
    }
}