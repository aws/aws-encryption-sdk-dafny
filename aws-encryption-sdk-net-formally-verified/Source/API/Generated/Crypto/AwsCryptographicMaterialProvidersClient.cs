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
        private Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient.AwsCryptographicMaterialProvidersClient _impl;

        public AwsCryptographicMaterialProvidersClient()
        {
            this._impl =
                new Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient.AwsCryptographicMaterialProvidersClient();
        }

        protected override Aws.Crypto.IKeyring _CreateStrictAwsKmsKeyring(
            Aws.Crypto.CreateStrictAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateStrictAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S30_CreateStrictAwsKmsKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateStrictAwsKmsKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateAwsKmsDiscoveryKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareStrictAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareStrictAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S38_CreateMrkAwareStrictAwsKmsKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateMrkAwareStrictAwsKmsKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareStrictMultiKeyring(
            Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareStrictMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S37_CreateMrkAwareStrictMultiKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateMrkAwareStrictMultiKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareDiscoveryAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S41_CreateMrkAwareDiscoveryAwsKmsKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateMrkAwareDiscoveryAwsKmsKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateMultiKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateRawAesKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.IKeyring _CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawRsaKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput(input);
            Dafny.Aws.Crypto.IKeyring internalOutput =
                this._impl.CreateRawRsaKeyring(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(internalOutput);
        }

        protected override Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
            Dafny.Aws.Crypto.ICryptographicMaterialsManager internalOutput =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                internalOutput);
        }

        protected override Aws.Crypto.CreateDefaultClientSupplierOutput _CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultClientSupplierInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S32_CreateDefaultClientSupplierInput(input);
            Dafny.Aws.Crypto._ICreateDefaultClientSupplierOutput internalOutput =
                this._impl.CreateDefaultClientSupplier(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S33_CreateDefaultClientSupplierOutput(internalOutput);
        }
    }
}