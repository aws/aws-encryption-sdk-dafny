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
    public class EncryptInput
    {
        public System.IO.MemoryStream Plaintext { get; private set; }
        public System.Collections.Generic.IDictionary<string, string> EncryptionContext { get; private set; }
        public ICryptographicMaterialsManager MaterialsManager { get; private set; }
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }

        public static IEncryptInputBuilder Builder()
        {
            return new EncryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptInputBuilder : IEncryptInputBuilder
        {
            private System.IO.MemoryStream Plaintext;
            private System.Collections.Generic.IDictionary<string, string> EncryptionContext;
            private ICryptographicMaterialsManager MaterialsManager;
            private AlgorithmSuiteId AlgorithmSuiteId;

            public IEncryptInputBuilder WithPlaintext(System.IO.MemoryStream value)
            {
                Plaintext = value;
                return this;
            }

            public IEncryptInputBuilder WithEncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
            {
                EncryptionContext = value;
                return this;
            }

            public IEncryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value)
            {
                MaterialsManager = value;
                return this;
            }

            public IEncryptInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public EncryptInput Build()
            {
                if (Plaintext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "plaintext"));
                }

                if (EncryptionContext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionContext"));
                }

                if (MaterialsManager == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materialsManager"));
                }

                return new EncryptInput
                {
                    Plaintext = (System.IO.MemoryStream) Plaintext,
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                    MaterialsManager = (ICryptographicMaterialsManager) MaterialsManager,
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId,
                };
            }
        }
    }

    public interface IEncryptInputBuilder
    {
        IEncryptInputBuilder WithPlaintext(System.IO.MemoryStream value);
        IEncryptInputBuilder WithEncryptionContext(System.Collections.Generic.IDictionary<string, string> value);
        IEncryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value);
        IEncryptInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        EncryptInput Build();
    }
}
