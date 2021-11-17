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
    public class DecryptMaterialsOutput
    {
        public DecryptionMaterials DecryptionMaterials { get; private set; }

        public static IDecryptMaterialsOutputBuilder Builder()
        {
            return new DecryptMaterialsOutputBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptMaterialsOutputBuilder : IDecryptMaterialsOutputBuilder
        {
            private DecryptionMaterials DecryptionMaterials;

            public IDecryptMaterialsOutputBuilder WithDecryptionMaterials(DecryptionMaterials value)
            {
                DecryptionMaterials = value;
                return this;
            }

            public DecryptMaterialsOutput Build()
            {
                if (DecryptionMaterials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "decryptionMaterials"));
                }

                return new DecryptMaterialsOutput
                {
                    DecryptionMaterials = (DecryptionMaterials) DecryptionMaterials,
                };
            }
        }
    }

    public interface IDecryptMaterialsOutputBuilder
    {
        IDecryptMaterialsOutputBuilder WithDecryptionMaterials(DecryptionMaterials value);
        DecryptMaterialsOutput Build();
    }
}