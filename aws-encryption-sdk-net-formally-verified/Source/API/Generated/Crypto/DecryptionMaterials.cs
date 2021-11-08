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
    public class DecryptionMaterials
    {
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }
        public System.Collections.Generic.IDictionary<string, string> EncryptionContext { get; private set; }
        public System.IO.MemoryStream PlaintextDataKey { get; private set; }
        public System.IO.MemoryStream VerificationKey { get; private set; }

        public static IDecryptionMaterialsBuilder Builder()
        {
            return new DecryptionMaterialsBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptionMaterialsBuilder : IDecryptionMaterialsBuilder
        {
            private AlgorithmSuiteId AlgorithmSuiteId;
            private System.Collections.Generic.IDictionary<string, string> EncryptionContext;
            private System.IO.MemoryStream PlaintextDataKey;
            private System.IO.MemoryStream VerificationKey;

            public IDecryptionMaterialsBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public IDecryptionMaterialsBuilder WithEncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
            {
                EncryptionContext = value;
                return this;
            }

            public IDecryptionMaterialsBuilder WithPlaintextDataKey(System.IO.MemoryStream value)
            {
                PlaintextDataKey = value;
                return this;
            }

            public IDecryptionMaterialsBuilder WithVerificationKey(System.IO.MemoryStream value)
            {
                VerificationKey = value;
                return this;
            }

            public DecryptionMaterials Build()
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

                return new DecryptionMaterials
                {
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId,
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                    PlaintextDataKey = (System.IO.MemoryStream) PlaintextDataKey,
                    VerificationKey = (System.IO.MemoryStream) VerificationKey,
                };
            }
        }
    }

    public interface IDecryptionMaterialsBuilder
    {
        IDecryptionMaterialsBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        IDecryptionMaterialsBuilder WithEncryptionContext(System.Collections.Generic.IDictionary<string, string> value);
        IDecryptionMaterialsBuilder WithPlaintextDataKey(System.IO.MemoryStream value);
        IDecryptionMaterialsBuilder WithVerificationKey(System.IO.MemoryStream value);
        DecryptionMaterials Build();
    }
}
