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
    public class OnEncryptOutput
    {
        public EncryptionMaterials Materials { get; private set; }

        public static IOnEncryptOutputBuilder Builder()
        {
            return new OnEncryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class OnEncryptOutputBuilder : IOnEncryptOutputBuilder
        {
            private EncryptionMaterials Materials;

            public IOnEncryptOutputBuilder WithMaterials(EncryptionMaterials value)
            {
                Materials = value;
                return this;
            }

            public OnEncryptOutput Build()
            {
                if (Materials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materials"));
                }

                return new OnEncryptOutput
                {
                    Materials = (EncryptionMaterials) Materials,
                };
            }
        }
    }

    public interface IOnEncryptOutputBuilder
    {
        IOnEncryptOutputBuilder WithMaterials(EncryptionMaterials value);
        OnEncryptOutput Build();
    }
}