// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    internal class Keyring : KeyringBase
    {
        internal readonly Dafny.Aws.EncryptionSdk.Core.IKeyring _impl;

        internal Keyring(Dafny.Aws.EncryptionSdk.Core.IKeyring impl)
        {
            this._impl = impl;
        }

        protected override AWS.EncryptionSDK.Core.OnDecryptOutput _OnDecrypt(
            AWS.EncryptionSDK.Core.OnDecryptInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._IOnDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnDecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnDecryptOutput,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnDecrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnDecryptOutput(result.dtor_value);
        }

        protected override AWS.EncryptionSDK.Core.OnEncryptOutput _OnEncrypt(
            AWS.EncryptionSDK.Core.OnEncryptInput input)
        {
            Dafny.Aws.EncryptionSdk.Core._IOnEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S14_OnEncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core._IOnEncryptOutput,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnEncrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S15_OnEncryptOutput(result.dtor_value);
        }
    }
}
