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
    public class CreateDefaultCryptographicMaterialsManagerInput
    {
        public IKeyring Keyring { get; private set; }

        public static ICreateDefaultCryptographicMaterialsManagerInputBuilder Builder()
        {
            return new CreateDefaultCryptographicMaterialsManagerInputBuilder();
        }

        public void Validate()
        {
        }

        private class
            CreateDefaultCryptographicMaterialsManagerInputBuilder :
                ICreateDefaultCryptographicMaterialsManagerInputBuilder
        {
            private IKeyring Keyring;

            public ICreateDefaultCryptographicMaterialsManagerInputBuilder WithKeyring(IKeyring value)
            {
                Keyring = value;
                return this;
            }

            public CreateDefaultCryptographicMaterialsManagerInput Build()
            {
                if (Keyring == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "keyring"));
                }

                return new CreateDefaultCryptographicMaterialsManagerInput
                {
                    Keyring = (IKeyring) Keyring,
                };
            }
        }
    }

    public interface ICreateDefaultCryptographicMaterialsManagerInputBuilder
    {
        ICreateDefaultCryptographicMaterialsManagerInputBuilder WithKeyring(IKeyring value);
        CreateDefaultCryptographicMaterialsManagerInput Build();
    }
}