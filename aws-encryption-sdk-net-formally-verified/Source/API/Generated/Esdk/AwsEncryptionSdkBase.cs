// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Aws.EncryptionSdk.Core;
using
    Aws.EncryptionSdk
    ;

namespace Aws.EncryptionSdk
{
    public abstract class AwsEncryptionSdkBase : IAwsEncryptionSdk
    {
        public Aws.EncryptionSdk.EncryptOutput Encrypt(Aws.EncryptionSdk.EncryptInput input)
        {
            input.Validate();
            return _Encrypt(input);
        }

        protected abstract Aws.EncryptionSdk.EncryptOutput _Encrypt(Aws.EncryptionSdk.EncryptInput input);

        public Aws.EncryptionSdk.DecryptOutput Decrypt(Aws.EncryptionSdk.DecryptInput input)
        {
            input.Validate();
            return _Decrypt(input);
        }

        protected abstract Aws.EncryptionSdk.DecryptOutput _Decrypt(Aws.EncryptionSdk.DecryptInput input);
    }
}
