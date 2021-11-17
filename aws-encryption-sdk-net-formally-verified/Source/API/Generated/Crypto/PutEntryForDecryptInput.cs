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
    public class PutEntryForDecryptInput
    {
        public System.IO.MemoryStream Identifier { get; private set; }
        public DecryptionMaterials DecryptionMaterials { get; private set; }

        public static IPutEntryForDecryptInputBuilder Builder()
        {
            return new PutEntryForDecryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class PutEntryForDecryptInputBuilder : IPutEntryForDecryptInputBuilder
        {
            private System.IO.MemoryStream Identifier;
            private DecryptionMaterials DecryptionMaterials;

            public IPutEntryForDecryptInputBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public IPutEntryForDecryptInputBuilder WithDecryptionMaterials(DecryptionMaterials value)
            {
                DecryptionMaterials = value;
                return this;
            }

            public PutEntryForDecryptInput Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                if (DecryptionMaterials == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "decryptionMaterials"));
                }

                return new PutEntryForDecryptInput
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                    DecryptionMaterials = (DecryptionMaterials) DecryptionMaterials,
                };
            }
        }
    }

    public interface IPutEntryForDecryptInputBuilder
    {
        IPutEntryForDecryptInputBuilder WithIdentifier(System.IO.MemoryStream value);
        IPutEntryForDecryptInputBuilder WithDecryptionMaterials(DecryptionMaterials value);
        PutEntryForDecryptInput Build();
    }
}