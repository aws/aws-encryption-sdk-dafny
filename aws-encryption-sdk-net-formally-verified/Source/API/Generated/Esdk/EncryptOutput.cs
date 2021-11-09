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
    public class EncryptOutput
    {
        public System.IO.MemoryStream Ciphertext { get; private set; }

        public static IEncryptOutputBuilder Builder()
        {
            return new EncryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptOutputBuilder : IEncryptOutputBuilder
        {
            private System.IO.MemoryStream Ciphertext;

            public IEncryptOutputBuilder WithCiphertext(System.IO.MemoryStream value)
            {
                Ciphertext = value;
                return this;
            }

            public EncryptOutput Build()
            {
                if (Ciphertext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "ciphertext"));
                }

                return new EncryptOutput
                {
                    Ciphertext = (System.IO.MemoryStream) Ciphertext,
                };
            }
        }
    }

    public interface IEncryptOutputBuilder
    {
        IEncryptOutputBuilder WithCiphertext(System.IO.MemoryStream value);
        EncryptOutput Build();
    }
}
