// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk.Core
    ;

namespace Aws.EncryptionSdk.Core
{
    internal class AwsCryptographicMaterialProviders : AwsCryptographicMaterialProvidersBase
    {
        internal Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders _impl { get; }

        internal AwsCryptographicMaterialProviders(Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders impl)
        {
            this._impl = impl;
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkMultiKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateAwsKmsMrkMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateRawRsaKeyring(
            Aws.EncryptionSdk.Core.CreateRawRsaKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateRawRsaKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawRsaKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawRsaKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateRawAesKeyring(
            Aws.EncryptionSdk.Core.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateRawAesKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateRawAesKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_CreateAwsKmsMrkKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryKeyringInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N13_encryptionSdk__N4_core__S36_CreateAwsKmsMrkDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IClientSupplier _CreateDefaultClientSupplier(
            Aws.EncryptionSdk.Core.CreateDefaultClientSupplierInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateDefaultClientSupplierInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S32_CreateDefaultClientSupplierInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IClientSupplier,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultClientSupplier(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S23_ClientSupplierReference(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S33_CreateAwsKmsDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N13_encryptionSdk__N4_core__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.ICryptographicMaterialsManager
            _CreateDefaultCryptographicMaterialsManager(
                Aws.EncryptionSdk.Core.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N13_encryptionSdk__N4_core__S47_CreateDefaultCryptographicMaterialsManagerInput(
                        input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion
                .FromDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateCryptographicMaterialsManagerOutput(
                    result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S24_CreateAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateMultiKeyring(
            Aws.EncryptionSdk.Core.CreateMultiKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S23_CreateMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMultiKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S29_CreateAwsKmsMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }

        protected override Aws.EncryptionSdk.Core.IKeyring _CreateAwsKmsMrkDiscoveryMultiKeyring(
            Aws.EncryptionSdk.Core.CreateAwsKmsMrkDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._ICreateAwsKmsMrkDiscoveryMultiKeyringInput internalInput =
                TypeConversion
                    .ToDafny_N3_aws__N13_encryptionSdk__N4_core__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IKeyring,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S19_CreateKeyringOutput(
                result.dtor_value);
        }
    }
}
