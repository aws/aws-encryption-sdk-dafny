// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Collections.Generic;
using Aws.Crypto;
using
    Aws.Esdk
    ;

// TODO need to update code gen to produce this file instead of I/Client/Base files

namespace Aws.Esdk
{
    public class AwsEncryptionSdkClientFactory
    {
        public static Aws.Esdk.IAwsEncryptionSdkClient MakeAwsEncryptionSdkClient(
            Aws.Esdk.AwsEncryptionSdkClientConfig input)
        {
            Dafny.Aws.Esdk.AwsEncryptionSdkClientFactory.AwsEncryptionSdkClientFactory impl = new Dafny.Aws.Esdk.AwsEncryptionSdkClientFactory.AwsEncryptionSdkClientFactory();
            Dafny.Aws.Esdk._IAwsEncryptionSdkClientConfig internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk.IAwsEncryptionSdkClient,
                Dafny.Aws.Esdk.IAwsEncryptionSdkClientException> result =
                impl.MakeAwsEncryptionSdkClient(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkClientException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S31_AwsEncryptionSdkClientReference(result.dtor_value);
        }
    }
}
