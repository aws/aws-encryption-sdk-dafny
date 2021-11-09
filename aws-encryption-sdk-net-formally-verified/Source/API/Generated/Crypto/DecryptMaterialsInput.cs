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
    public class DecryptMaterialsInput
    {
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }
        public System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys { get; private set; }
        public System.Collections.Generic.IDictionary<string, string> EncryptionContext { get; private set; }

        public static IDecryptMaterialsInputBuilder Builder()
        {
            return new DecryptMaterialsInputBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptMaterialsInputBuilder : IDecryptMaterialsInputBuilder
        {
            private AlgorithmSuiteId AlgorithmSuiteId;
            private System.Collections.Generic.IList<EncryptedDataKey> EncryptedDataKeys;
            private System.Collections.Generic.IDictionary<string, string> EncryptionContext;

            public IDecryptMaterialsInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public IDecryptMaterialsInputBuilder WithEncryptedDataKeys(
                System.Collections.Generic.IList<EncryptedDataKey> value)
            {
                EncryptedDataKeys = value;
                return this;
            }

            public IDecryptMaterialsInputBuilder WithEncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
            {
                EncryptionContext = value;
                return this;
            }

            public DecryptMaterialsInput Build()
            {
                if (AlgorithmSuiteId == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "algorithmSuiteId"));
                }

                if (EncryptedDataKeys == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptedDataKeys"));
                }

                if (EncryptionContext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionContext"));
                }

                return new DecryptMaterialsInput
                {
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId,
                    EncryptedDataKeys = (System.Collections.Generic.IList<EncryptedDataKey>) EncryptedDataKeys,
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                };
            }
        }
    }

    public interface IDecryptMaterialsInputBuilder
    {
        IDecryptMaterialsInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        IDecryptMaterialsInputBuilder WithEncryptedDataKeys(System.Collections.Generic.IList<EncryptedDataKey> value);

        IDecryptMaterialsInputBuilder WithEncryptionContext(
            System.Collections.Generic.IDictionary<string, string> value);

        DecryptMaterialsInput Build();
    }
}
