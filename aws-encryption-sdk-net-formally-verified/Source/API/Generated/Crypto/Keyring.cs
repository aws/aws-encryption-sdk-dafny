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
    internal class Keyring : KeyringBase
    {
        internal Dafny.Aws.Encryption.Core.IKeyring _impl { get; }

        internal Keyring(Dafny.Aws.Encryption.Core.IKeyring impl)
        {
            this._impl = impl;
        }

        protected override Aws.Encryption.Core.OnEncryptOutput _OnEncrypt(Aws.Encryption.Core.OnEncryptInput input)
        {
            Dafny.Aws.Encryption.Core._IOnEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S14_OnEncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core._IOnEncryptOutput,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnEncrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S15_OnEncryptOutput(result.dtor_value);
        }

        protected override Aws.Encryption.Core.OnDecryptOutput _OnDecrypt(Aws.Encryption.Core.OnDecryptInput input)
        {
            Dafny.Aws.Encryption.Core._IOnDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__N4_core__S14_OnDecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.Core._IOnDecryptOutput,
                Dafny.Aws.Encryption.Core.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnDecrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__N4_core__S15_OnDecryptOutput(result.dtor_value);
        }
    }
}
