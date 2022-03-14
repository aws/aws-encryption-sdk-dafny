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
    public static class AwsEncryptionSdkFactory
    {
        static Dafny.Aws.Encryption.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory _impl =
            new Dafny.Aws.Encryption.AwsEncryptionSdkFactory.AwsEncryptionSdkFactory();

        public static Aws.Encryption.IAwsEncryptionSdk CreateDefaultAwsEncryptionSdk()
        {
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.IAwsEncryptionSdk,
                Dafny.Aws.Encryption.IAwsEncryptionSdkException> result = _impl.CreateDefaultAwsEncryptionSdk();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkReference(result.dtor_value);
        }

        public static Aws.Encryption.IAwsEncryptionSdk CreateAwsEncryptionSdk(
            Aws.Encryption.AwsEncryptionSdkConfig input)
        {
            Dafny.Aws.Encryption._IAwsEncryptionSdkConfig internalInput =
                TypeConversion.ToDafny_N3_aws__N10_encryption__S22_AwsEncryptionSdkConfig(input);
            Wrappers_Compile._IResult<Dafny.Aws.Encryption.IAwsEncryptionSdk,
                Dafny.Aws.Encryption.IAwsEncryptionSdkException> result = _impl.CreateAwsEncryptionSdk(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkBaseException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N10_encryption__S25_AwsEncryptionSdkReference(result.dtor_value);
        }
    }
}
