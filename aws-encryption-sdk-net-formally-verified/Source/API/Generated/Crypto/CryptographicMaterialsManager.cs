// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    internal class CryptographicMaterialsManager : CryptographicMaterialsManagerBase
    {
        internal readonly Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager _impl;

        internal CryptographicMaterialsManager(Dafny.Aws.EncryptionSdk.Core.ICryptographicMaterialsManager impl)
        {
            this._impl = impl;
        }

        protected override AWS.EncryptionSDK.Core.DecryptMaterialsOutput _DecryptMaterials(
            AWS.EncryptionSDK.Core.DecryptMaterialsInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S21_DecryptMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IDecryptMaterialsOutput,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.DecryptMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S22_DecryptMaterialsOutput(
                result.dtor_value);
        }

        protected override AWS.EncryptionSDK.Core.GetEncryptionMaterialsOutput _GetEncryptionMaterials(
            AWS.EncryptionSDK.Core.GetEncryptionMaterialsInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S27_GetEncryptionMaterialsInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IGetEncryptionMaterialsOutput,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.GetEncryptionMaterials(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S28_GetEncryptionMaterialsOutput(
                result.dtor_value);
        }
    }
}
