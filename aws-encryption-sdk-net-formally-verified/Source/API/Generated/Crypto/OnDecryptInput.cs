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
    public class OnDecryptInput
    {
        public DecryptionMaterials Materials { get; private set; }
        public System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys { get; private set; }

        public static IOnDecryptInputBuilder Builder()
        {
            return new OnDecryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class OnDecryptInputBuilder : IOnDecryptInputBuilder
        {
            private DecryptionMaterials Materials;
            private System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys;

            public IOnDecryptInputBuilder WithMaterials(DecryptionMaterials value)
            {
                Materials = value;
                return this;
            }

            public IOnDecryptInputBuilder WithEncryptedDataKeys(
                System.Collections.Generic.IList<EncryptedDataKey> value)
            {
                EncryptedDataKeys = value;
                return this;
            }

            public OnDecryptInput Build()
            {
                if (Materials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materials"));
                }

                if (EncryptedDataKeys == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptedDataKeys"));
                }

                return new OnDecryptInput
                {
                    Materials = (DecryptionMaterials) Materials,
                    EncryptedDataKeys = (System.Collections.Generic.IList<EncryptedDataKey>) EncryptedDataKeys,
                };
            }
        }
    }

    public interface IOnDecryptInputBuilder
    {
        IOnDecryptInputBuilder WithMaterials(DecryptionMaterials value);
        IOnDecryptInputBuilder WithEncryptedDataKeys(System.Collections.Generic.IList<EncryptedDataKey> value);
        OnDecryptInput Build();
    }
}
