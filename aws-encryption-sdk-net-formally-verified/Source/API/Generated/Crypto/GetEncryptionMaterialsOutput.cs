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
    public class GetEncryptionMaterialsOutput
    {
        public EncryptionMaterials EncryptionMaterials { get; private set; }

        public static IGetEncryptionMaterialsOutputBuilder Builder()
        {
            return new GetEncryptionMaterialsOutputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEncryptionMaterialsOutputBuilder : IGetEncryptionMaterialsOutputBuilder
        {
            private EncryptionMaterials EncryptionMaterials;

            public IGetEncryptionMaterialsOutputBuilder WithEncryptionMaterials(EncryptionMaterials value)
            {
                EncryptionMaterials = value;
                return this;
            }

            public GetEncryptionMaterialsOutput Build()
            {
                if (EncryptionMaterials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionMaterials"));
                }

                return new GetEncryptionMaterialsOutput
                {
                    EncryptionMaterials = (EncryptionMaterials) EncryptionMaterials,
                };
            }
        }
    }

    public interface IGetEncryptionMaterialsOutputBuilder
    {
        IGetEncryptionMaterialsOutputBuilder WithEncryptionMaterials(EncryptionMaterials value);
        GetEncryptionMaterialsOutput Build();
    }
}
