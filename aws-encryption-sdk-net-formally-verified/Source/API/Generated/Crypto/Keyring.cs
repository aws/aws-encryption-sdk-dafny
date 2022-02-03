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
    internal class Keyring : KeyringBase
    {
        internal Dafny.Aws.Crypto.IKeyring _impl { get; }

        internal Keyring(Dafny.Aws.Crypto.IKeyring impl)
        {
            this._impl = impl;
        }

        protected override Aws.Crypto.OnEncryptOutput _OnEncrypt(Aws.Crypto.OnEncryptInput input)
        {
            Dafny.Aws.Crypto._IOnEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IOnEncryptOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnEncrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput(result.dtor_value);
        }

        protected override Aws.Crypto.OnDecryptOutput _OnDecrypt(Aws.Crypto.OnDecryptInput input)
        {
            Dafny.Aws.Crypto._IOnDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Crypto._IOnDecryptOutput,
                Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> result =
                this._impl.OnDecrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion
                    .FromDafny_CommonError_AwsCryptographicMaterialProvidersException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(result.dtor_value);
        }
    }
}
