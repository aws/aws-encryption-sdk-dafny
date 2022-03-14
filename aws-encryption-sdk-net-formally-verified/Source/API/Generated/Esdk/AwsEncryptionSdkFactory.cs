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
    public static class AwsEncryptionSdkFactory
    {
        static Dafny.Aws.Esdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory _impl =
            new Dafny.Aws.Esdk.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();

        public static Aws.Esdk.IAwsEncryptionSdk CreateDefaultAwsEncryptionSdk()
        {
            Wrappers_Compile._IResult<Dafny.Aws.Esdk.IAwsEncryptionSdk, Dafny.Aws.Esdk.IAwsEncryptionSdkException>
                result = _impl.CreateDefaultAwsEncryptionSdk();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S25_AwsEncryptionSdkReference(result.dtor_value);
        }

        public static Aws.Esdk.IAwsEncryptionSdk CreateAwsEncryptionSdk(Aws.Esdk.AwsEncryptionSdkConfig input)
        {
            Dafny.Aws.Esdk._IAwsEncryptionSdkConfig internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S22_AwsEncryptionSdkConfig(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk.IAwsEncryptionSdk, Dafny.Aws.Esdk.IAwsEncryptionSdkException>
                result = _impl.CreateAwsEncryptionSdk(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S25_AwsEncryptionSdkReference(result.dtor_value);
        }
    }
}
