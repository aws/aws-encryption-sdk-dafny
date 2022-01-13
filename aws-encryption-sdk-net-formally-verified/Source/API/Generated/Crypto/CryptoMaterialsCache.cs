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
    internal class CryptoMaterialsCache : CryptoMaterialsCacheBase
    {
        internal Dafny.Aws.Crypto.ICryptoMaterialsCache _impl { get; }

        internal CryptoMaterialsCache(Dafny.Aws.Crypto.ICryptoMaterialsCache impl)
        {
            this._impl = impl;
        }

        protected override Aws.Crypto.DeleteEntryOutput _DeleteEntry(Aws.Crypto.DeleteEntryInput input)
        {
            Dafny.Aws.Crypto._IDeleteEntryInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S16_DeleteEntryInput(input);
            Dafny.Aws.Crypto._IDeleteEntryOutput internalOutput =
                this._impl.DeleteEntry(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S17_DeleteEntryOutput(internalOutput);
        }

        protected override Aws.Crypto.PutEntryForEncryptOutput _PutEntryForEncrypt(
            Aws.Crypto.PutEntryForEncryptInput input)
        {
            Dafny.Aws.Crypto._IPutEntryForEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForEncryptInput(input);
            Dafny.Aws.Crypto._IPutEntryForEncryptOutput internalOutput =
                this._impl.PutEntryForEncrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForEncryptOutput(internalOutput);
        }

        protected override Aws.Crypto.GetEntryForDecryptOutput _GetEntryForDecrypt(
            Aws.Crypto.GetEntryForDecryptInput input)
        {
            Dafny.Aws.Crypto._IGetEntryForDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForDecryptInput(input);
            Dafny.Aws.Crypto._IGetEntryForDecryptOutput internalOutput =
                this._impl.GetEntryForDecrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForDecryptOutput(internalOutput);
        }

        protected override Aws.Crypto.GetEntryForEncryptOutput _GetEntryForEncrypt(
            Aws.Crypto.GetEntryForEncryptInput input)
        {
            Dafny.Aws.Crypto._IGetEntryForEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_GetEntryForEncryptInput(input);
            Dafny.Aws.Crypto._IGetEntryForEncryptOutput internalOutput =
                this._impl.GetEntryForEncrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_GetEntryForEncryptOutput(internalOutput);
        }

        protected override Aws.Crypto.PutEntryForDecryptOutput _PutEntryForDecrypt(
            Aws.Crypto.PutEntryForDecryptInput input)
        {
            Dafny.Aws.Crypto._IPutEntryForDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N6_crypto__S23_PutEntryForDecryptInput(input);
            Dafny.Aws.Crypto._IPutEntryForDecryptOutput internalOutput =
                this._impl.PutEntryForDecrypt(internalInput);
            return TypeConversion.FromDafny_N3_aws__N6_crypto__S24_PutEntryForDecryptOutput(internalOutput);
        }
    }
}
