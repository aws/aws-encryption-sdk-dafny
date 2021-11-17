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
    public class DecryptOutput
    {
        public System.IO.MemoryStream Plaintext { get; private set; }

        public static IDecryptOutputBuilder Builder()
        {
            return new DecryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class DecryptOutputBuilder : IDecryptOutputBuilder
        {
            private System.IO.MemoryStream Plaintext;

            public IDecryptOutputBuilder WithPlaintext(System.IO.MemoryStream value)
            {
                Plaintext = value;
                return this;
            }

            public DecryptOutput Build()
            {
                if (Plaintext == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "plaintext"));
                }

                return new DecryptOutput
                {
                    Plaintext = (System.IO.MemoryStream) Plaintext,
                };
            }
        }
    }

    public interface IDecryptOutputBuilder
    {
        IDecryptOutputBuilder WithPlaintext(System.IO.MemoryStream value);
        DecryptOutput Build();
    }
}