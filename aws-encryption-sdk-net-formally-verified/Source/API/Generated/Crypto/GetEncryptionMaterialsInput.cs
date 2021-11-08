// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:19:52.740808

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEncryptionMaterialsInput
    {
        public System.Collections.Generic.IDictionary<string, string> EncryptionContext { get; private set; }
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }
        public long? MaxPlaintextLength { get; private set; }

        public static IGetEncryptionMaterialsInputBuilder Builder()
        {
            return new GetEncryptionMaterialsInputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEncryptionMaterialsInputBuilder : IGetEncryptionMaterialsInputBuilder
        {
            private System.Collections.Generic.IDictionary<string, string> EncryptionContext;
            private AlgorithmSuiteId AlgorithmSuiteId;
            private long? MaxPlaintextLength;

            public IGetEncryptionMaterialsInputBuilder WithEncryptionContext(
                System.Collections.Generic.IDictionary<string, string> value)
            {
                EncryptionContext = value;
                return this;
            }

            public IGetEncryptionMaterialsInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public IGetEncryptionMaterialsInputBuilder WithMaxPlaintextLength(long? value)
            {
                MaxPlaintextLength = value;
                return this;
            }

            public GetEncryptionMaterialsInput Build()
            {
                if (EncryptionContext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptionContext"));
                }

                return new GetEncryptionMaterialsInput
                {
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId,
                    MaxPlaintextLength = (long?) MaxPlaintextLength,
                };
            }
        }
    }

    public interface IGetEncryptionMaterialsInputBuilder
    {
        IGetEncryptionMaterialsInputBuilder WithEncryptionContext(
            System.Collections.Generic.IDictionary<string, string> value);

        IGetEncryptionMaterialsInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        IGetEncryptionMaterialsInputBuilder WithMaxPlaintextLength(long? value);
        GetEncryptionMaterialsInput Build();
    }
}
