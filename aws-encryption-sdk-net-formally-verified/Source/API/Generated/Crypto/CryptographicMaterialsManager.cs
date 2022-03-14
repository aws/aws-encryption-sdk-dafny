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
    internal class CryptographicMaterialsManager : CryptographicMaterialsManagerBase
    {
        internal Dafny.Aws.Crypto.ICryptographicMaterialsManager _impl { get; }

        internal CryptographicMaterialsManager(Dafny.Aws.Crypto.ICryptographicMaterialsManager impl)
        {
            this._impl = impl;
        }

        protected override Aws.Crypto.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            Aws.Crypto.GetEncryptionMaterialsInput input)
        {
            Dafny.Aws.Crypto._IGetEncryptionMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IGetEncryptionMaterialsOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.GetEncryptionMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(result.dtor_value);
        }

        protected override Aws.Crypto.DecryptMaterialsOutput _DecryptMaterials(Aws.Crypto.DecryptMaterialsInput input)
        {
            Dafny.Aws.Crypto._IDecryptMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IDecryptMaterialsOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.DecryptMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(result.dtor_value);
        }
    }
}
