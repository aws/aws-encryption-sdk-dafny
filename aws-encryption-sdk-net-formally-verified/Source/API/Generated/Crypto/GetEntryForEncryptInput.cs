// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class GetEntryForEncryptInput
    {
        public System.IO.MemoryStream Identifier { get; private set; }

        public static IGetEntryForEncryptInputBuilder Builder()
        {
            return new GetEntryForEncryptInputBuilder();
        }

        public void Validate()
        {
        }

        private class GetEntryForEncryptInputBuilder : IGetEntryForEncryptInputBuilder
        {
            private System.IO.MemoryStream Identifier;

            public IGetEntryForEncryptInputBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public GetEntryForEncryptInput Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                return new GetEntryForEncryptInput
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                };
            }
        }
    }

    public interface IGetEntryForEncryptInputBuilder
    {
        IGetEntryForEncryptInputBuilder WithIdentifier(System.IO.MemoryStream value);
        GetEntryForEncryptInput Build();
    }
}