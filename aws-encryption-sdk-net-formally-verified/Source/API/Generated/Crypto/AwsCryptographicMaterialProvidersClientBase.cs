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
    public abstract class AwsCryptographicMaterialProvidersClientBase : IAwsCryptographicMaterialProviders
    {
        protected AwsCryptographicMaterialProvidersClientBase()
        {
        }

        public IKeyring CreateRawAesKeyring(CreateRawAesKeyringInput input)
        {
            input.Validate();
            return _CreateRawAesKeyring(input);
        }

        protected abstract IKeyring _CreateRawAesKeyring(CreateRawAesKeyringInput input);

        public ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
            CreateDefaultCryptographicMaterialsManagerInput input)
        {
            input.Validate();
            return _CreateDefaultCryptographicMaterialsManager(input);
        }

        protected abstract ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            CreateDefaultCryptographicMaterialsManagerInput input);
    }
}