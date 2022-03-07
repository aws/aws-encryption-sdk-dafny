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
    public class AwsEncryptionSdkClient : AwsEncryptionSdkClientBase
    {
        private Dafny.Aws.Esdk.AwsEncryptionSdkClient.AwsEncryptionSdkClient _impl;

        public AwsEncryptionSdkClient(Aws.Esdk.AwsEncryptionSdkClientConfig config) : base(config)
        {
            this._impl =
                new Dafny.Aws.Esdk.AwsEncryptionSdkClient.AwsEncryptionSdkClient();
            this._impl.__ctor(TypeConversion.ToDafny_N3_aws__N4_esdk__S28_AwsEncryptionSdkClientConfig(config));
        }

        protected override Aws.Esdk.EncryptOutput _Encrypt(Aws.Esdk.EncryptInput input)
        {
            Dafny.Aws.Esdk._IEncryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S12_EncryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk._IEncryptOutput, Dafny.Aws.Esdk.IAwsEncryptionSdkException>
                result = this._impl.Encrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_EncryptOutput(result.dtor_value);
        }

        protected override Aws.Esdk.DecryptOutput _Decrypt(Aws.Esdk.DecryptInput input)
        {
            Dafny.Aws.Esdk._IDecryptInput internalInput =
                TypeConversion.ToDafny_N3_aws__N4_esdk__S12_DecryptInput(input);
            Wrappers_Compile._IResult<Dafny.Aws.Esdk._IDecryptOutput, Dafny.Aws.Esdk.IAwsEncryptionSdkException>
                result = this._impl.Decrypt(internalInput);
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsEncryptionSdkException(result.dtor_error);
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_DecryptOutput(result.dtor_value);
        }
    }
}
