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
    public class DeleteEntryInput
    {
        public System.IO.MemoryStream Identifier { get; private set; }

        public static IDeleteEntryInputBuilder Builder()
        {
            return new DeleteEntryInputBuilder();
        }

        public void Validate()
        {
        }

        private class DeleteEntryInputBuilder : IDeleteEntryInputBuilder
        {
            private System.IO.MemoryStream Identifier;

            public IDeleteEntryInputBuilder WithIdentifier(System.IO.MemoryStream value)
            {
                Identifier = value;
                return this;
            }

            public DeleteEntryInput Build()
            {
                if (Identifier == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "identifier"));
                }

                return new DeleteEntryInput
                {
                    Identifier = (System.IO.MemoryStream) Identifier,
                };
            }
        }
    }

    public interface IDeleteEntryInputBuilder
    {
        IDeleteEntryInputBuilder WithIdentifier(System.IO.MemoryStream value);
        DeleteEntryInput Build();
    }
}