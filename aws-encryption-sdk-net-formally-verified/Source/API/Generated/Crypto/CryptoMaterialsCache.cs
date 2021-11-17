// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.880813

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    internal class CryptoMaterialsCache : CryptoMaterialsCacheBase
    {
        internal Dafny.Aws.Crypto.ICryptoMaterialsCache _impl { get; }

        internal CryptoMaterialsCache(Dafny.Aws.Crypto.ICryptoMaterialsCache impl)
        {
            this._impl = impl;
        }

        protected override DeleteEntryOutput _DeleteEntry(DeleteEntryInput input)
        {
            Dafny.Aws.Crypto.DeleteEntryInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput(input);
            Dafny.Aws.Crypto.DeleteEntryOutput internalOutput =
                this._impl.DeleteEntry(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S17_DeleteEntryOutput(internalOutput);
        }

        protected override PutEntryForEncryptOutput _PutEntryForEncrypt(PutEntryForEncryptInput input)
        {
            Dafny.Aws.Crypto.PutEntryForEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput(input);
            Dafny.Aws.Crypto.PutEntryForEncryptOutput internalOutput =
                this._impl.PutEntryForEncrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForEncryptOutput(internalOutput);
        }

        protected override GetEntryForDecryptOutput _GetEntryForDecrypt(GetEntryForDecryptInput input)
        {
            Dafny.Aws.Crypto.GetEntryForDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput(input);
            Dafny.Aws.Crypto.GetEntryForDecryptOutput internalOutput =
                this._impl.GetEntryForDecrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput(internalOutput);
        }

        protected override GetEntryForEncryptOutput _GetEntryForEncrypt(GetEntryForEncryptInput input)
        {
            Dafny.Aws.Crypto.GetEntryForEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput(input);
            Dafny.Aws.Crypto.GetEntryForEncryptOutput internalOutput =
                this._impl.GetEntryForEncrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput(internalOutput);
        }

        protected override PutEntryForDecryptOutput _PutEntryForDecrypt(PutEntryForDecryptInput input)
        {
            Dafny.Aws.Crypto.PutEntryForDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput(input);
            Dafny.Aws.Crypto.PutEntryForDecryptOutput internalOutput =
                this._impl.PutEntryForDecrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForDecryptOutput(internalOutput);
        }
    }
}