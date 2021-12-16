// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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

        protected override Aws.Crypto.IKeyring _CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input)
        {
            Dafny.Aws.Crypto.CreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateMultiKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Crypto.CreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateRawAesKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
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
