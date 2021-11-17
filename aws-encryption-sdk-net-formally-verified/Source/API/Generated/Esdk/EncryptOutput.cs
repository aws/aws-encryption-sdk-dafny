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
    public class EncryptOutput
    {
        public System.IO.MemoryStream EncryptedMessage { get; private set; }

        public static IEncryptOutputBuilder Builder()
        {
            return new EncryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class EncryptOutputBuilder : IEncryptOutputBuilder
        {
            private System.IO.MemoryStream EncryptedMessage;

            public IEncryptOutputBuilder WithEncryptedMessage(System.IO.MemoryStream value)
            {
                EncryptedMessage = value;
                return this;
            }

            public EncryptOutput Build()
            {
                if (EncryptedMessage == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "encryptedMessage"));
                }

                return new EncryptOutput
                {
                    EncryptedMessage = (System.IO.MemoryStream) EncryptedMessage,
                };
            }
        }
    }

    public interface IEncryptOutputBuilder
    {
        IEncryptOutputBuilder WithEncryptedMessage(System.IO.MemoryStream value);
        EncryptOutput Build();
    }
}