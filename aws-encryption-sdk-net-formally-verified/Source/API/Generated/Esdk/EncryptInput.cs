// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:32:59.305823

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
        public IKeyring Keyring { get; private set; }
        public AlgorithmSuiteId AlgorithmSuiteId { get; private set; }
        public int? FrameLength { get; private set; }

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
            private IKeyring Keyring;
            private AlgorithmSuiteId AlgorithmSuiteId;
            private int? FrameLength;

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

            public IEncryptInputBuilder WithKeyring(IKeyring value)
            {
                Keyring = value;
                return this;
            }

            public IEncryptInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value)
            {
                AlgorithmSuiteId = value;
                return this;
            }

            public IEncryptInputBuilder WithFrameLength(int? value)
            {
                FrameLength = value;
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

                if (Keyring == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyring"));
                }

                return new EncryptInput
                {
                    Plaintext = (System.IO.MemoryStream) Plaintext,
                    EncryptionContext = (System.Collections.Generic.IDictionary<string, string>) EncryptionContext,
                    MaterialsManager = (ICryptographicMaterialsManager) MaterialsManager, Keyring = (IKeyring) Keyring,
                    AlgorithmSuiteId = (AlgorithmSuiteId) AlgorithmSuiteId, FrameLength = (int?) FrameLength,
                };
            }
        }
    }

    public interface IEncryptInputBuilder
    {
        IEncryptInputBuilder WithPlaintext(System.IO.MemoryStream value);
        IEncryptInputBuilder WithEncryptionContext(System.Collections.Generic.IDictionary<string, string> value);
        IEncryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value);
        IEncryptInputBuilder WithKeyring(IKeyring value);
        IEncryptInputBuilder WithAlgorithmSuiteId(AlgorithmSuiteId value);
        IEncryptInputBuilder WithFrameLength(int? value);
        EncryptInput Build();
    }
}