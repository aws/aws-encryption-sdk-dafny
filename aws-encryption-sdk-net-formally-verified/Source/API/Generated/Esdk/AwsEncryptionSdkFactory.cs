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
    public static class AwsEncryptionSdkFactory
    {
        static Dafny.Aws.EncryptionSdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory _impl =
            new Dafny.Aws.EncryptionSdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();

        public static Aws.EncryptionSdk.IAwsEncryptionSdk CreateDefaultAwsEncryptionSdk()
        {
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.IAwsEncryptionSdk,
                Dafny.Aws.EncryptionSdk.IAwsEncryptionSdkException> result = _impl.CreateDefaultAwsEncryptionSdk();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__S25_AwsEncryptionSdkReference(result.dtor_value);
        }

        public static Aws.EncryptionSdk.IAwsEncryptionSdk CreateAwsEncryptionSdk(
            Aws.EncryptionSdk.AwsEncryptionSdkConfig input)
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
