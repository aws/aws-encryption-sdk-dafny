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
    internal class AwsCryptographicMaterialProviders : AwsCryptographicMaterialProvidersBase
    {
        internal Dafny.Aws.Crypto.IAwsCryptographicMaterialProviders _impl { get; }

        internal AwsCryptographicMaterialProviders(Dafny.Aws.Crypto.IAwsCryptographicMaterialProviders impl)
        {
            this._impl = impl;
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsMrkKeyring(Aws.Crypto.CreateAwsKmsMrkKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsMrkKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S27_CreateAwsKmsMrkKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsMultiKeyring(Aws.Crypto.CreateAwsKmsMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S29_CreateAwsKmsMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawAesKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawRsaKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawRsaKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S36_CreateAwsKmsMrkDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsMrkDiscoveryMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.ICryptographicMaterialsManager,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsKeyring(Aws.Crypto.CreateAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IClientSupplier _CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultClientSupplierInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S32_CreateDefaultClientSupplierInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IClientSupplier,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultClientSupplier(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.Crypto.CreateAwsKmsMrkMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsMrkMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S32_CreateAwsKmsMrkMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }
    }
}
