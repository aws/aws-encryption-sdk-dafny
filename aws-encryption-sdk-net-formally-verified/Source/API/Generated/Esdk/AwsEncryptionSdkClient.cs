// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    internal class AwsEncryptionSdkClient : AwsEncryptionSdkClientBase
    {
        internal Dafny.Aws.Esdk.IAwsEncryptionSdkClient _impl { get; }

        internal AwsEncryptionSdkClient(Dafny.Aws.Esdk.IAwsEncryptionSdkClient impl)
        {
            this._impl = impl;
        }

        protected override Aws.Esdk.EncryptOutput _Encrypt(Aws.Esdk.EncryptInput input)
        {
            Dafny.Aws.Esdk._IEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S12_EncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk._IEncryptOutput, Dafny.Aws.Esdk.IAwsEncryptionSdkFactoryException>
                result = this._impl.Encrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkFactoryException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_EncryptOutput(result.dtor_value);
        }

        protected override Aws.Esdk.DecryptOutput _Decrypt(Aws.Esdk.DecryptInput input)
        {
            Dafny.Aws.Esdk._IDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S12_DecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk._IDecryptOutput, Dafny.Aws.Esdk.IAwsEncryptionSdkFactoryException>
                result = this._impl.Decrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkFactoryException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_DecryptOutput(result.dtor_value);
        }
    }
}
