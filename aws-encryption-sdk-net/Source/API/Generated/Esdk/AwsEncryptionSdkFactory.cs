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
    public static class AwsEncryptionSdkFactory
    {
        static readonly Dafny.Aws.EncryptionSdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory _impl =
            new Dafny.Aws.EncryptionSdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();

        public static AWS.EncryptionSDK.IAwsEncryptionSdk CreateDefaultAwsEncryptionSdk()
        {
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk,
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException> result = _impl.CreateDefaultAwsEncryptionSdk();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkReference(result.dtor_value);
        }

        public static AWS.EncryptionSDK.IAwsEncryptionSdk CreateAwsEncryptionSdk(
            AWS.EncryptionSDK.AwsEncryptionSdkConfig input)
        {
            Dafny.Aws.EncryptionSdk._IAwsEncryptionSdkConfig internalInput =
                TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__S22_AwsEncryptionSdkConfig(input);
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk,
                    Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException>
                result = _impl.CreateAwsEncryptionSdk(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkReference(result.dtor_value);
        }
    }
}
