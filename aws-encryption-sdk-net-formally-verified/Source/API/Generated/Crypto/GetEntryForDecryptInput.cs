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
    public class GetEntryForDecryptInput
    {
        public System.IO.MemoryStream Identifier { get; private set; }

        public static IGetEntryForDecryptInputBuilder Builder()
        {
            return new GetEntryForDecryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEntryForDecryptInputBuilder : IGetEntryForDecryptInputBuilder
        {
            private System.IO.MemoryStream Identifier;

            public IGetEntryForDecryptInputBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public GetEntryForDecryptInput Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                return new GetEntryForDecryptInput
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                };
            }
        }
    }

    public interface IGetEntryForDecryptInputBuilder
    {
        IGetEntryForDecryptInputBuilder WithIdentifier(System.IO.MemoryStream value);
        GetEntryForDecryptInput Build();
    }
}
