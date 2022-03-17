// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk
    ;

namespace Aws.EncryptionSdk
{
    internal class AwsEncryptionSdk : AwsEncryptionSdkBase
    {
        internal Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk _impl { get; }

        internal AwsEncryptionSdk(Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk impl)
        {
            this._impl = impl;
        }

        protected override Aws.EncryptionSdk.DecryptOutput _Decrypt(Aws.EncryptionSdk.DecryptInput input)
        {
            Dafny.Aws.EncryptionSdk._IDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk._IDecryptOutput,
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException> result = this._impl.Decrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput(result.dtor_value);
        }

        protected override Aws.EncryptionSdk.EncryptOutput _Encrypt(Aws.EncryptionSdk.EncryptInput input)
        {
            Dafny.Aws.EncryptionSdk._IEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__S12_EncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk._IEncryptOutput,
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException> result = this._impl.Encrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S13_EncryptOutput(result.dtor_value);
        }
    }
}
