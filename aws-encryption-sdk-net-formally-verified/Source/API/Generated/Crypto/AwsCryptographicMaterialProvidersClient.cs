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
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateStrictAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
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
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareStrictAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareStrictAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S38_CreateMrkAwareStrictAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateMrkAwareStrictAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S19_CreateKeyringOutput(result.dtor_value);
        }

        protected override Aws.Crypto.IKeyring _CreateMrkAwareDiscoveryAwsKmsKeyring(
            Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput input)
        {
            Dafny.Aws.Crypto._ICreateMrkAwareDiscoveryAwsKmsKeyringInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S41_CreateMrkAwareDiscoveryAwsKmsKeyringInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto.IKeyring,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.CreateMrkAwareDiscoveryAwsKmsKeyring(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
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
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
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
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
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
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
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
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S41_CreateCryptographicMaterialsManagerOutput(
                result.dtor_value);
        }

        protected override Aws.Crypto.ImportPublicRSAKeyOutput _ImportPublicRSAKey(Aws.Crypto.ImportRSAKeyInput input)
        {
            Dafny.Aws.Crypto._IImportRSAKeyInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S17_ImportRSAKeyInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IImportPublicRSAKeyOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.ImportPublicRSAKey(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_ImportPublicRSAKeyOutput(result.dtor_value);
        }

        protected override Aws.Crypto.ImportPrivateRSAKeyOutput _ImportPrivateRSAKey(Aws.Crypto.ImportRSAKeyInput input)
        {
            Dafny.Aws.Crypto._IImportRSAKeyInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S17_ImportRSAKeyInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IImportPrivateRSAKeyOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.ImportPrivateRSAKey(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S25_ImportPrivateRSAKeyOutput(result.dtor_value);
        }
    }
}
