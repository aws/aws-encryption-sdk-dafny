// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Encryption;
using Aws.Encryption.Core;
using
    Aws.Encryption
    ;

namespace Aws.Encryption
{
    internal class AwsEncryptionSdk : AwsEncryptionSdkBase
    {
        internal Dafny.Aws.Encryption.IAwsEncryptionSdk _impl { get; }

        internal AwsEncryptionSdk(Dafny.Aws.Encryption.IAwsEncryptionSdk impl)
        {
            this._impl = impl;
        }

        protected override Aws.Encryption.EncryptOutput _Encrypt(Aws.Encryption.EncryptInput input)
        {
            Dafny.Aws.Encryption._IEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__S12_EncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption._IEncryptOutput,
                Dafny.Aws.Encryption.IAwsEncryptionSdkException> result = this._impl.Encrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__S13_EncryptOutput(result.dtor_value);
        }

        protected override Aws.Encryption.DecryptOutput _Decrypt(Aws.Encryption.DecryptInput input)
        {
            Dafny.Aws.Encryption._IDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__S12_DecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption._IDecryptOutput,
                Dafny.Aws.Encryption.IAwsEncryptionSdkException> result = this._impl.Decrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__S13_DecryptOutput(result.dtor_value);
        }
    }
}
