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
    public class OnDecryptOutput
    {
        public DecryptionMaterials Materials { get; private set; }

        public static IOnDecryptOutputBuilder Builder()
        {
            return new OnDecryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class OnDecryptOutputBuilder : IOnDecryptOutputBuilder
        {
            private DecryptionMaterials Materials;

            public IOnDecryptOutputBuilder WithMaterials(DecryptionMaterials value)
            {
                Materials = value;
                return this;
            }

            public OnDecryptOutput Build()
            {
                if (Materials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materials"));
                }

                return new OnDecryptOutput
                {
                    Materials = (DecryptionMaterials) Materials,
                };
            }
        }
    }

    public interface IOnDecryptOutputBuilder
    {
        IOnDecryptOutputBuilder WithMaterials(DecryptionMaterials value);
        OnDecryptOutput Build();
    }
}