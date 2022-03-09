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
    internal class AwsCryptographicMaterialProvidersClient : AwsCryptographicMaterialProvidersClientBase
    {
        internal Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClient _impl { get; }

        internal AwsCryptographicMaterialProvidersClient(Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClient impl)
        {
            this._impl = impl;
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S33_CreateAwsKmsDiscoveryKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateAwsKmsDiscoveryKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateRawAesKeyring(Aws.Crypto.CreateRawAesKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawAesKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawAesKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateRawAesKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateRawRsaKeyring(Aws.Crypto.CreateRawRsaKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateRawRsaKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S24_CreateRawRsaKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateRawRsaKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMultiKeyring(Aws.Crypto.CreateMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_CreateMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.ICryptographicMaterialsManager _CreateDefaultCryptographicMaterialsManager(
            Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultCryptographicMaterialsManagerInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S47_CreateDefaultCryptographicMaterialsManagerInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.ICryptographicMaterialsManager,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateDefaultCryptographicMaterialsManager(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareDiscoveryAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S41_CreateMrkAwareDiscoveryAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateMrkAwareDiscoveryAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareStrictAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareStrictAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S38_CreateMrkAwareStrictAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateMrkAwareStrictAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareStrictMultiKeyring(
            Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareStrictMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S37_CreateMrkAwareStrictMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateMrkAwareStrictMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IClientSupplier _CreateDefaultClientSupplier(
            Aws.Crypto.CreateDefaultClientSupplierInput input)
        {
            Dafny.Aws.Crypto._ICreateDefaultClientSupplierInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S32_CreateDefaultClientSupplierInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IClientSupplier,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateDefaultClientSupplier(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S23_ClientSupplierReference(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateStrictAwsKmsKeyring(
            Aws.Crypto.CreateStrictAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateStrictAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S30_CreateStrictAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateStrictAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateAwsKmsDiscoveryMultiKeyring(
            Aws.Crypto.CreateAwsKmsDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateAwsKmsDiscoveryMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S38_CreateAwsKmsDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateAwsKmsDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateStrictAwsKmsMultiKeyring(
            Aws.Crypto.CreateStrictAwsKmsMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateStrictAwsKmsMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S35_CreateStrictAwsKmsMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateStrictAwsKmsMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareDiscoveryMultiKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareDiscoveryMultiKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S40_CreateMrkAwareDiscoveryMultiKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersClientFactoryException> result =
                this._impl.CreateMrkAwareDiscoveryMultiKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersClientFactoryException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }
    }
}
