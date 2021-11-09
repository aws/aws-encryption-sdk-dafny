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
    public class EncryptedDataKey
    {
        public string KeyProviderId { get; private set; }
        public string KeyProviderInfo { get; private set; }
        public System.IO.MemoryStream Ciphertext { get; private set; }

        public static IEncryptedDataKeyBuilder Builder()
        {
            return new EncryptedDataKeyBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptedDataKeyBuilder : IEncryptedDataKeyBuilder
        {
            private string KeyProviderId;
            private string KeyProviderInfo;
            private System.IO.MemoryStream Ciphertext;

            public IEncryptedDataKeyBuilder WithKeyProviderId(string value)
            {
                KeyProviderId = value;
                return this;
            }

            public IEncryptedDataKeyBuilder WithKeyProviderInfo(string value)
            {
                KeyProviderInfo = value;
                return this;
            }

            public IEncryptedDataKeyBuilder WithCiphertext(System.IO.MemoryStream value)
            {
                Ciphertext = value;
                return this;
            }

            public EncryptedDataKey Build()
            {
                if (KeyProviderId == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyProviderId"));
                }

                if (KeyProviderInfo == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyProviderInfo"));
                }

                if (Ciphertext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "ciphertext"));
                }

                return new EncryptedDataKey
                {
                    KeyProviderId = (string) KeyProviderId, KeyProviderInfo = (string) KeyProviderInfo,
                    Ciphertext = (System.IO.MemoryStream) Ciphertext,
                };
            }
        }
    }

    public interface IEncryptedDataKeyBuilder
    {
        IEncryptedDataKeyBuilder WithKeyProviderId(string value);
        IEncryptedDataKeyBuilder WithKeyProviderInfo(string value);
        IEncryptedDataKeyBuilder WithCiphertext(System.IO.MemoryStream value);
        EncryptedDataKey Build();
    }
}
