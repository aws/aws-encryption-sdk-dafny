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
    internal class CryptographicMaterialsManager : CryptographicMaterialsManagerBase
    {
        internal Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager _impl { get; }

        internal CryptographicMaterialsManager(Dafny.Aws.Encryption.Core.ICryptographicMaterialsManager impl)
        {
            this._impl = impl;
        }

        protected override Aws.Encryption.Core.DecryptMaterialsOutput _DecryptMaterials(
            Aws.Encryption.Core.DecryptMaterialsInput input)
        {
            Dafny.Aws.Encryption.Core._IDecryptMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S21_DecryptMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core._IDecryptMaterialsOutput,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.DecryptMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S22_DecryptMaterialsOutput(
                result.dtor_value);
        }

        protected override Aws.Encryption.Core.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            Aws.Encryption.Core.GetEncryptionMaterialsInput input)
        {
            Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S27_GetEncryptionMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core._IGetEncryptionMaterialsOutput,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.GetEncryptionMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S28_GetEncryptionMaterialsOutput(
                result.dtor_value);
        }
    }
}
