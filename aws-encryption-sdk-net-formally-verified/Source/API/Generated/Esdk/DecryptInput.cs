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
    public class DecryptInput
    {
        public System.IO.MemoryStream EncryptedMessage { get; private set; }
        public ICryptographicMaterialsManager MaterialsManager { get; private set; }
        public IKeyring Keyring { get; private set; }

        public static IDecryptInputBuilder Builder()
        {
            return new DecryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptInputBuilder : IDecryptInputBuilder
        {
            private System.IO.MemoryStream EncryptedMessage;
            private ICryptographicMaterialsManager MaterialsManager;
            private IKeyring Keyring;

            public IDecryptInputBuilder WithEncryptedMessage(System.IO.MemoryStream value)
            {
                EncryptedMessage = value;
                return this;
            }

            public IDecryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value)
            {
                MaterialsManager = value;
                return this;
            }

            public IDecryptInputBuilder WithKeyring(IKeyring value)
            {
                Keyring = value;
                return this;
            }

            public DecryptInput Build()
            {
                if (EncryptedMessage == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptedMessage"));
                }

                if (MaterialsManager == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "materialsManager"));
                }

                // TODO if statement manually removed
                // if (Keyring == null)
                // {
                //     throw new InvalidOperationException(
                //         String.Format("No value set for required field {0}", "keyring"));
                // }

                return new DecryptInput
                {
                    EncryptedMessage = (System.IO.MemoryStream) EncryptedMessage,
                    MaterialsManager = (ICryptographicMaterialsManager) MaterialsManager, Keyring = (IKeyring) Keyring,
                };
            }
        }
    }

    public interface IDecryptInputBuilder
    {
        IDecryptInputBuilder WithEncryptedMessage(System.IO.MemoryStream value);
        IDecryptInputBuilder WithMaterialsManager(ICryptographicMaterialsManager value);
        IDecryptInputBuilder WithKeyring(IKeyring value);
        DecryptInput Build();
    }
}