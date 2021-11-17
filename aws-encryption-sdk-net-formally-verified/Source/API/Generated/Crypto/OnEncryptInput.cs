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
    public class OnEncryptInput
    {
        public EncryptionMaterials Materials { get; private set; }

        public static IOnEncryptInputBuilder Builder()
        {
            return new OnEncryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class OnEncryptInputBuilder : IOnEncryptInputBuilder
        {
            private EncryptionMaterials Materials;

            public IOnEncryptInputBuilder WithMaterials(EncryptionMaterials value)
            {
                Materials = value;
                return this;
            }

            public OnEncryptInput Build()
            {
                if (Materials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materials"));
                }

                return new OnEncryptInput
                {
                    Materials = (EncryptionMaterials) Materials,
                };
            }
        }
    }

    public interface IOnEncryptInputBuilder
    {
        IOnEncryptInputBuilder WithMaterials(EncryptionMaterials value);
        OnEncryptInput Build();
    }
}