// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Encryption;
using Aws.Encryption.Core;
using
    Aws.Encryption.Core
    ;

namespace Aws.Encryption.Core
{
    internal class AwsCryptographicMaterialProviders : AwsCryptographicMaterialProvidersBase
    {
        internal Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProviders _impl { get; }

        internal AwsCryptographicMaterialProviders(Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProviders impl)
        {
            this._impl = impl;
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsKeyring(
            Aws.Encryption.Core.CreateAwsKmsKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.ICryptographicMaterialsManager
            _CreateDefaultCryptographicMaterialsManager(
                Aws.Encryption.Core.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N10_encryption__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                        input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion
                .FromDafny_N3_aws__N10_encryption__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                    result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateRawAesKeyring(
            Aws.Encryption.Core.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawAesKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawAesKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateRawRsaKeyring(
            Aws.Encryption.Core.CreateRawRsaKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateRawRsaKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S24_CreateRawRsaKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawRsaKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateMultiKeyring(
            Aws.Encryption.Core.CreateMultiKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S23_CreateMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N10_encryption__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S27_CreateAwsKmsMrkKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkMultiKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsMultiKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S29_CreateAwsKmsMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Encryption.Core.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N10_encryption__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.Encryption.Core.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateAwsKmsMrkDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IKeyring,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.IClientSupplier _CreateDefaultClientSupplier(
            Aws.Encryption.Core.CreateDefaultClientSupplierInput input)
        {
            Dafny.Aws.Encryption.Core._ICreateDefaultClientSupplierInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S32_CreateDefaultClientSupplierInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core.IClientSupplier,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultClientSupplier(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S23_ClientSupplierReference(
                result.dtor_value);
        }
    }
}
