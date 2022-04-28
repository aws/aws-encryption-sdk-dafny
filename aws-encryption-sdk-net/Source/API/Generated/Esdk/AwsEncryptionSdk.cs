// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;
using AWS.EncryptionSDK;

namespace AWS.EncryptionSDK
{
    internal class AwsEncryptionSdk : AwsEncryptionSdkBase
    {
        internal readonly Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk _impl;

        internal AwsEncryptionSdk(Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk impl)
        {
            this._impl = impl;
        }

        protected override AWS.EncryptionSDK.DecryptOutput _Decrypt(AWS.EncryptionSDK.DecryptInput input)
        {
            Dafny.Aws.EncryptionSdk._IDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__S12_DecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk._IDecryptOutput,
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException> result = this._impl.Decrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S13_DecryptOutput(result.dtor_value);
        }

        protected override AWS.EncryptionSDK.EncryptOutput _Encrypt(AWS.EncryptionSDK.EncryptInput input)
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
