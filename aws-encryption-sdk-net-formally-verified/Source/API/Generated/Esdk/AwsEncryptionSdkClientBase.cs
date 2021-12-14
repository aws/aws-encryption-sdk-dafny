// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.Crypto;
using
    Aws.Esdk
    ;

namespace Aws.Esdk
{
    public abstract class AwsEncryptionSdkClientBase : IAwsEncryptionSdk
    {
        protected AwsEncryptionSdkClientBase()
        {
        }

        public Aws.Esdk.EncryptOutput Encrypt(Aws.Esdk.EncryptInput input)
        {
            input.Validate();
            return _Encrypt(input);
        }

        protected abstract Aws.Esdk.EncryptOutput _Encrypt(Aws.Esdk.EncryptInput input);

        public Aws.Esdk.DecryptOutput Decrypt(Aws.Esdk.DecryptInput input)
        {
            input.Validate();
            return _Decrypt(input);
        }

        protected abstract Aws.Esdk.DecryptOutput _Decrypt(Aws.Esdk.DecryptInput input);
    }
}
