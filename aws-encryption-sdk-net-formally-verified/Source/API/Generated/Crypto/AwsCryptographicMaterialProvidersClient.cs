// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:21:59.752491

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class AwsCryptographicMaterialProvidersClient : AwsCryptographicMaterialProvidersClientBase
    {
        private Dafny.Aws.Crypto.MaterialProviders.Client.AwsCryptographicMaterialProvidersClient _impl;

        public AwsCryptographicMaterialProvidersClient()
        {
            this._impl =
                new Dafny.Aws.Crypto.MaterialProviders.Client.AwsCryptographicMaterialProvidersClient();
        }

        protected override IKeyring _CreateRawAesKeyring(CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Crypto.CreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateRawAesKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
            Dafny.Aws.Crypto.ICryptographicMaterialsManager internalOutput =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                internalOutput);
        }
    }
}
