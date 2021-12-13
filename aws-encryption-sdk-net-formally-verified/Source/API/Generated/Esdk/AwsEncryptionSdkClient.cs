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

        public AwsEncryptionSdkClient()
        {
            this._impl = new Dafny.Aws.Esdk.AwsEncryptionSdkClient.AwsEncryptionSdkClient();
        }

        protected override Aws.Esdk.EncryptOutput _Encrypt(Aws.Esdk.EncryptInput input)
        {
            Dafny.Aws.Esdk.EncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N4_esdk__S12_EncryptInput(input);
            Dafny.Aws.Esdk.EncryptOutput internalOutput =
            // TODO this line was manually updated
            DafnyFFI.ExtractResult(this._impl.Encrypt(internalInput));
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_EncryptOutput(internalOutput);
        }

        protected override Aws.Esdk.DecryptOutput _Decrypt(Aws.Esdk.DecryptInput input)
        {
            Dafny.Aws.Esdk.DecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N4_esdk__S12_DecryptInput(input);
            Dafny.Aws.Esdk.DecryptOutput internalOutput =
                // TODO this line was manually updated
                DafnyFFI.ExtractResult(this._impl.Decrypt(internalInput));
            return TypeConversion.FromDafny_N3_aws__N4_esdk__S13_DecryptOutput(internalOutput);
        }
    }
}