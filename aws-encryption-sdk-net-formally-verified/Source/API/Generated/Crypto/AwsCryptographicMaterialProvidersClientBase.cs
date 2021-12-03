// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-12-02T18:30:30.159384

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public abstract class AwsCryptographicMaterialProvidersClientBase : IAwsCryptographicMaterialProviders
    {
        protected AwsCryptographicMaterialProvidersClientBase()
        {
        }

        public Aws.Crypto.IKeyring CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input);

        public Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input);
    }
}
