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
    public class EncryptionMaterials
    {
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }
        public System.Collections.Generic.IDictionary<string, string> EncryptionContext { get; private set; }
        public System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys { get; private set; }
        public System.IO.MemoryStream PlaintextDataKey { get; private set; }
        public System.IO.MemoryStream SigningKey { get; private set; }

        public static IEncryptionMaterialsBuilder Builder()
        {
            return new EncryptionMaterialsBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptionMaterialsBuilder : IEncryptionMaterialsBuilder
        {
            private AlgorithmSuiteId AlgorithmSuiteId;
            private System.Collections.Generic.IDictionary<string, string> EncryptionContext;
            private System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys;
            private System.IO.MemoryStream PlaintextDataKey;
            private System.IO.MemoryStream SigningKey;

            public IEncryptionMaterialsBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public IEncryptionMaterialsBuilder WithEncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
            {
                EncryptionContext = value;
                return this;
            }

            public IEncryptionMaterialsBuilder WithEncryptedDataKeys(
                System.Collections.Generic.IList<EncryptedDataKey> value)
            {
                EncryptedDataKeys = value;
                return this;
            }

            public IEncryptionMaterialsBuilder WithPlaintextDataKey(System.IO.MemoryStream value)
            {
                PlaintextDataKey = value;
                return this;
            }

            public IEncryptionMaterialsBuilder WithSigningKey(System.IO.MemoryStream value)
            {
                SigningKey = value;
                return this;
            }

            public EncryptionMaterials Build()
            {
                if (AlgorithmSuiteId == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "algorithmSuiteId"));
                }

                if (EncryptionContext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionContext"));
                }

                if (EncryptedDataKeys == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptedDataKeys"));
                }

                return new EncryptionMaterials
                {
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId,
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                    EncryptedDataKeys = (System.Collections.Generic.IList<EncryptedDataKey>) EncryptedDataKeys,
                    PlaintextDataKey = (System.IO.MemoryStream) PlaintextDataKey,
                    SigningKey = (System.IO.MemoryStream) SigningKey,
                };
            }
        }
    }

    public interface IEncryptionMaterialsBuilder
    {
        IEncryptionMaterialsBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        IEncryptionMaterialsBuilder WithEncryptionContext(System.Collections.Generic.IDictionary<string, string> value);
        IEncryptionMaterialsBuilder WithEncryptedDataKeys(System.Collections.Generic.IList<EncryptedDataKey> value);
        IEncryptionMaterialsBuilder WithPlaintextDataKey(System.IO.MemoryStream value);
        IEncryptionMaterialsBuilder WithSigningKey(System.IO.MemoryStream value);
        EncryptionMaterials Build();
    }
}
