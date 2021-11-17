// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:23:01.04064

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

        protected override GetEncryptionMaterialsOutput _GetEncryptionMaterials(GetEncryptionMaterialsInput input)
        {
            Dafny.Aws.Crypto.GetEncryptionMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S27_GetEncryptionMaterialsInput(input);
            Dafny.Aws.Crypto.GetEncryptionMaterialsOutput internalOutput =
                // TODO this line was manually updated
                DafnyFFI.ExtractResult(this._impl.GetEncryptionMaterials(internalInput));
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S28_GetEncryptionMaterialsOutput(internalOutput);
        }

        protected override DecryptMaterialsOutput _DecryptMaterials(DecryptMaterialsInput input)
        {
            Dafny.Aws.Crypto.DecryptMaterialsInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S21_DecryptMaterialsInput(input);
            Dafny.Aws.Crypto.DecryptMaterialsOutput internalOutput =
                // TODO this line was manually updated
                DafnyFFI.ExtractResult(this._impl.DecryptMaterials(internalInput));
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S22_DecryptMaterialsOutput(internalOutput);
        }
    }
}