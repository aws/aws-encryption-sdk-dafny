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
    public class CreateRawAesKeyringInput
    {
        public string KeyNamespace { get; private set; }
        public string KeyName { get; private set; }
        public System.IO.MemoryStream WrappingKey { get; private set; }
        public AesWrappingAlg WrappingAlg { get; private set; }

        public static ICreateRawAesKeyringInputBuilder Builder()
        {
            return new CreateRawAesKeyringInputBuilder();
        }

        public void Validate()
        {
        }

        private class CreateRawAesKeyringInputBuilder : ICreateRawAesKeyringInputBuilder
        {
            private string KeyNamespace;
            private string KeyName;
            private System.IO.MemoryStream WrappingKey;
            private AesWrappingAlg WrappingAlg;

            public ICreateRawAesKeyringInputBuilder WithKeyNamespace(string value)
            {
                KeyNamespace = value;
                return this;
            }

            public ICreateRawAesKeyringInputBuilder WithKeyName(string value)
            {
                KeyName = value;
                return this;
            }

            public ICreateRawAesKeyringInputBuilder WithWrappingKey(System.IO.MemoryStream value)
            {
                WrappingKey = value;
                return this;
            }

            public ICreateRawAesKeyringInputBuilder WithWrappingAlg(AesWrappingAlg value)
            {
                WrappingAlg = value;
                return this;
            }

            public CreateRawAesKeyringInput Build()
            {
                if (KeyNamespace == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyNamespace"));
                }

                if (KeyName == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyName"));
                }

                if (WrappingKey == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "wrappingKey"));
                }

                if (WrappingAlg == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "wrappingAlg"));
                }

                return new CreateRawAesKeyringInput
                {
                    KeyNamespace = (string) KeyNamespace, KeyName = (string) KeyName,
                    WrappingKey = (System.IO.MemoryStream) WrappingKey, WrappingAlg = (AesWrappingAlg) WrappingAlg,
                };
            }
        }
    }

    public interface ICreateRawAesKeyringInputBuilder
    {
        ICreateRawAesKeyringInputBuilder WithKeyNamespace(string value);
        ICreateRawAesKeyringInputBuilder WithKeyName(string value);
        ICreateRawAesKeyringInputBuilder WithWrappingKey(System.IO.MemoryStream value);
        ICreateRawAesKeyringInputBuilder WithWrappingAlg(AesWrappingAlg value);
        CreateRawAesKeyringInput Build();
    }
}
