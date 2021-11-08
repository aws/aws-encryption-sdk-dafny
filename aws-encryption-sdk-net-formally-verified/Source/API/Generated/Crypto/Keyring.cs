// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:21:59.752491

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

        protected override OnEncryptOutput _OnEncrypt(OnEncryptInput input)
        {
            Dafny.Aws.Crypto.OnEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S14_OnEncryptInput(input);
            Dafny.Aws.Crypto.OnEncryptOutput internalOutput =
                // TODO this line was manually updated
                DafnyFFI.ExtractResult(this._impl.OnEncrypt(internalInput));
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S15_OnEncryptOutput(internalOutput);
        }

        protected override OnDecryptOutput _OnDecrypt(OnDecryptInput input)
        {
            Dafny.Aws.Crypto.OnDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S14_OnDecryptInput(input);
            Dafny.Aws.Crypto.OnDecryptOutput internalOutput =
                // TODO this line was manually updated
                DafnyFFI.ExtractResult(this._impl.OnDecrypt(internalInput));
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S15_OnDecryptOutput(internalOutput);
        }
    }
}
