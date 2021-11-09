// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:22:03.283903

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public class DecryptInput
    {
        public System.IO.MemoryStream Ciphertext { get; private set; }
        public ICryptographicMaterialsManager MaterialsManager { get; private set; }

        public static IDecryptInputBuilder Builder()
        {
            return new DecryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptInputBuilder : IDecryptInputBuilder
        {
            private System.IO.MemoryStream Ciphertext;
            private ICryptographicMaterialsManager MaterialsManager;

            public IDecryptInputBuilder WithCiphertext(System.IO.MemoryStream value)
            {
                Ciphertext = value;
                return this;
            }

            public IDecryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value)
            {
                MaterialsManager = value;
                return this;
            }

            public DecryptInput Build()
            {
                if (Ciphertext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "ciphertext"));
                }

                if (MaterialsManager == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materialsManager"));
                }

                return new DecryptInput
                {
                    Ciphertext = (System.IO.MemoryStream) Ciphertext,
                    MaterialsManager = (ICryptographicMaterialsManager) MaterialsManager,
                };
            }
        }
    }

    public interface IDecryptInputBuilder
    {
        IDecryptInputBuilder WithCiphertext(System.IO.MemoryStream value);
        IDecryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value);
        DecryptInput Build();
    }
}
